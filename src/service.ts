import * as ts from 'typescript';
import * as vscode from 'vscode';
import { join as joinPath } from 'path';

import { throwError, isUndefined, assertNever, curry, isRestParameter } from './utils';
import { error as logError } from './log';
import { TextChange, Service, FileChangeType, FileChangeTypes, Decoration, Position, Configuration } from './types';

interface ServiceContext {
    readonly rootPath: string;
    readonly configuration: Configuration;
    readonly sourceFilesCache: Map<string, ts.SourceFile>;
    readonly updateProgram: () => void;
    readonly getCommittedSourceFilesCache: () => Map<string, ts.SourceFile>;
    readonly getProgram: () => ts.Program;
    readonly getOptions: () => ts.CompilerOptions;
    readonly getTypeChecker: () => ts.TypeChecker;
    readonly getRootFileNames: () => ReadonlyArray<string>;
}

export function createService(
    rootPath: string,
    configuration: Configuration,
    onUpdate: () => void
): Service {
    const context = createServiceContext(
        rootPath,
        configuration,
        getDelayedOnUpdate(configuration.updateDelay, onUpdate));

    return {
        getDecorations: curry(getDecorations, context),
        notifyFileChange: curry(notifyFileChange, context),
        notifyDocumentChange: curry(notifyDocumentChange, context)
    };
}

function getDelayedOnUpdate(delay: number, onUpdate: () => void): () => void {
    if (delay === 0) { return onUpdate; }

    let updateTimeout: NodeJS.Timer | undefined = undefined;
    return () => {
        if (updateTimeout !== undefined) {
            clearTimeout(updateTimeout);
        }

        updateTimeout = setTimeout(onUpdate, delay);
    };
}

function createServiceContext(
    rootPath: string,
    configuration: Configuration,
    onUpdate: () => void
): ServiceContext {
    const sourceFilesCache = new Map<string, ts.SourceFile>();
    let committedSourceFilesCache = new Map<string, ts.SourceFile>();
    let program: ts.Program = createProgram(rootPath, committedSourceFilesCache, sourceFilesCache);
    const context: ServiceContext = {
        rootPath,
        configuration,
        sourceFilesCache,
        updateProgram: getDelayedOnUpdate(
            configuration.compileDelay, 
            () => {
                ts.createSourceFile
                committedSourceFilesCache = new Map<string, ts.SourceFile>(context.sourceFilesCache);
                updateProgram(() => context, newProgram => program = newProgram, onUpdate);
            }
        ),
        getCommittedSourceFilesCache: () => committedSourceFilesCache,
        getProgram: () => program,
        getOptions: () => program.getCompilerOptions(),
        getTypeChecker: () => program.getTypeChecker(),
        getRootFileNames: () => program.getRootFileNames()
    };
    return context;
}

function createProgram(rootPath: string, committedSourceFilesCache: Map<string, ts.SourceFile>, sourceFilesCache: Map<string, ts.SourceFile>, oldProgram?: ts.Program): ts.Program {
    const { fileNames, options } = getParsedCommandLine(rootPath);
    const compilerHost = createCompilerHost(options, committedSourceFilesCache, sourceFilesCache);
    const program = ts.createProgram(fileNames, options, compilerHost, oldProgram);
    return program;
}

function updateProgram(
    getContext: () => ServiceContext,
    setProgram: (newProgram: ts.Program) => void,
    onUpdate: () => void
): void {
    const context = getContext();
    const program = createProgram(context.rootPath, context.getCommittedSourceFilesCache(), context.sourceFilesCache, context.getProgram());
    setProgram(program);
    onUpdate();
}

let queue: Set<() => void> | undefined = undefined;
function queueWork(fn: () => void): void {
    if(queue === undefined) {
        queue = new Set([fn]);
        processQueue();
    } else {
        queue.add(fn);
    }
}

function processQueue(): void {
    setTimeout(() => {
        if(queue === undefined) return;
        if(queue.size === 0) {
            queue = undefined;
            return;
        }
        const start = Date.now();
        for(const item of queue) {
            item();
            queue.delete(item);
            if(Date.now() - start > 100) {
                break;
            }
        }
        processQueue();
    }, 0);
}

const INCOMPLETE_TYPE = Symbol("incomplete") as unknown as ts.Type;
const INCOMPLETE_TYPENAME = "...";

const typeAtLocationCache = new WeakMap<ts.Node, ts.Type>();
function getTypeAtLocation(typeChecker: ts.TypeChecker, node: ts.Node): ts.Type {
    const cacheEntry = typeAtLocationCache.get(node);
    if(cacheEntry !== undefined) return cacheEntry;
    queueWork(() => {
        typeAtLocationCache.set(node, typeChecker.getTypeAtLocation(node));
    });
    return INCOMPLETE_TYPE;
}

const typeNameCache = new WeakMap<ts.Type, string>();
function getShortTypeName(typeChecker: ts.TypeChecker, type: ts.Type, enclosingDeclaration?: ts.Node): string {
    let typeName = typeNameCache.get(type);
    if (typeName !== undefined) return typeName;
    queueWork(() => {
        typeNameCache.set(type, typeChecker.typeToString(
            type,
            enclosingDeclaration,
            ts.TypeFormatFlags.WriteArrowStyleSignature |
            ts.TypeFormatFlags.UseAliasDefinedOutsideCurrentScope
        ));
    });
    return INCOMPLETE_TYPENAME;
}

const longTypeNameCache = new WeakMap<ts.Type, string>();
function getLongTypeName(typeChecker: ts.TypeChecker, type: ts.Type, enclosingDeclaration?: ts.Node): string {
    let longTypeName = longTypeNameCache.get(type);
    if (longTypeName !== undefined) return longTypeName;
    queueWork(() => {
        longTypeNameCache.set(type, typeChecker.typeToString(
            type,
            enclosingDeclaration, 
            ts.TypeFormatFlags.UseFullyQualifiedType |
            ts.TypeFormatFlags.NoTruncation |
            ts.TypeFormatFlags.UseStructuralFallback |
            ts.TypeFormatFlags.AllowUniqueESSymbolType |
            ts.TypeFormatFlags.WriteArrowStyleSignature |
            ts.TypeFormatFlags.WriteTypeArgumentsOfSignature
        ).replace(/;(\s(?=\s*\}))?/g, ";\n"));
    });
    return INCOMPLETE_TYPENAME;
}


function getDecorations(
    context: ServiceContext,
    fileName: string
): ReadonlyArray<Decoration> {
    const sourceFile = context.getCommittedSourceFilesCache().get(fileName);
    if (!sourceFile) {
        logError(`Failed to find source file '${fileName}' in cache.`);
        return [];
    }

    const typeChecker = context.getTypeChecker();
    const configuration = context.configuration;
    const result: Decoration[] = [];
    const skipTypes = new WeakSet<ts.Node>();
    aux(sourceFile);
    return result;

    function aux(node: ts.Node): void {
        node.forEachChild(aux);

        if(skipTypes.has(node)) return;

        try {
            if (ts.isVariableDeclaration(node) && !node.type) {
                const isFunction = node.initializer && ts.isFunctionLike(node.initializer);
                const shouldAddDecoration = isFunction
                    ? context.configuration.features.functionVariableType
                    : context.configuration.features.variableType;
                if (shouldAddDecoration) {
                    result.push(getDecoration(sourceFile!, typeChecker, configuration, node.name));
                }
            } else if (ts.isPropertySignature(node) && !node.type && context.configuration.features.propertyType) {
                result.push(getDecoration(sourceFile!, typeChecker, configuration, node.name))
            } else if (ts.isParameter(node) && !node.type && context.configuration.features.functionParameterType) {
                result.push(getDecoration(sourceFile!, typeChecker, configuration, node.name))
            } else if (ts.isFunctionDeclaration(node) && !node.type && context.configuration.features.functionReturnType) {
                const signature = typeChecker.getSignatureFromDeclaration(node);
                result.push(getDecoration(sourceFile!, typeChecker, configuration, node, node.body, signature && signature.getReturnType(), false, false));
            } else if (ts.isMethodDeclaration(node) && !node.type && context.configuration.features.functionReturnType) {
                const signature = typeChecker.getSignatureFromDeclaration(node);
                result.push(getDecoration(sourceFile!, typeChecker, configuration, node, node.body, signature && signature.getReturnType(), false, false));
            } else if (ts.isArrowFunction(node) && !node.type && context.configuration.features.functionReturnType) {
                const signature = typeChecker.getSignatureFromDeclaration(node);
                const returnsFunction = ts.isFunctionLike(node.body);
                if (!returnsFunction) {
                    result.push(getDecoration(sourceFile!, typeChecker, configuration, node, node.equalsGreaterThanToken, signature && signature.getReturnType(), node.parameters.length === 1, false));
                }
            } else if (ts.isObjectBindingPattern(node) && context.configuration.features.objectPatternType) {
                node.forEachChild(child => {
                    if(skipTypes.has(child)) return;
                    if (ts.isBindingElement(child)) {
                        result.push(getDecoration(sourceFile!, typeChecker, configuration, child));
                    }
                });
                if (node.parent) skipTypes.add(node.parent);
            } else if (ts.isArrayBindingPattern(node) && context.configuration.features.arrayPatternType) {
                node.forEachChild(child => {
                    if(skipTypes.has(child)) return;
                    if (ts.isBindingElement(child)) {
                        result.push(getDecoration(sourceFile!, typeChecker, configuration, child));
                    }
                });
                if (node.parent) skipTypes.add(node.parent);
            } else if (ts.isObjectLiteralExpression(node) && context.configuration.features.objectLiteralType) {
                let current = node.parent;
                if (current && ts.isParenthesizedExpression(current))
                    current = current.parent;
                if (current && ts.isReturnStatement(current))
                    current = current.parent;
                while(current && (
                    ts.isBlock(current) ||
                    ts.isIfStatement(current)
                )) current = current.parent;
                if (current &&  ts.isFunctionLike(current)) {
                    const signature = typeChecker.getSignatureFromDeclaration(current);
                    if(signature) {
                        const returnObject = signature.getReturnType();
                        let numberOfTypes = 0;
                        node.forEachChild(child => {
                            if ((
                                ts.isPropertyAssignment(child) ||
                                ts.isShorthandPropertyAssignment(child)
                             ) && ts.isIdentifier(child.name)) {
                                const symbol = returnObject.getProperty(child.name.text);
                                if (symbol && symbol.valueDeclaration) {
                                    numberOfTypes++;
                                    const type = getTypeAtLocation(typeChecker, symbol.valueDeclaration);
                                    if (type) {
                                        result.push(getDecoration(sourceFile!, typeChecker, configuration, child.name, undefined, type));
                                    }
                                }
                            }
                        });
                        if (current && numberOfTypes > 0 && numberOfTypes === returnObject.getProperties().length) skipTypes.add(current);
                    }
                }
            } else if ((ts.isCallExpression(node) || ts.isNewExpression(node)) && node.arguments && node.arguments.length > 0 && context.configuration.features.parameterName) {
                const resolvedSignature = typeChecker.getResolvedSignature(node);
                if (resolvedSignature) {
                    for (let i = 0; i < node.arguments.length; ++i) {
                        const argument = node.arguments[i];
                        const parameter = resolvedSignature.parameters[i];
                        if (parameter) {
                            const parameterName = (isRestParameter(parameter) ? '...' : '') + parameter.name;
                            if (parameterName !== argument.getText()) {
                                result.push({
                                    textBefore: `${parameterName}: `,
                                    textAfter: '',
                                    startPosition: sourceFile!.getLineAndCharacterOfPosition(argument.pos + argument.getLeadingTriviaWidth()),
                                    endPosition: sourceFile!.getLineAndCharacterOfPosition(argument.end),
                                    isWarning: false,
                                    isIncomplete: false
                                });
                            }
                        }
                    }
                }
            }
        } catch(e) {
            logError(e.message);
        }
    }
}

function getDecoration(
    sourceFile: ts.SourceFile,
    typeChecker: ts.TypeChecker,
    configuration: Configuration,
    node: ts.Node,
    endNode: ts.Node | undefined = undefined,
    type: ts.Type = getTypeAtLocation(typeChecker, node),
    wrap: boolean = false,
    hover: boolean = true
): Decoration {
    const leadingTriviaWidth = node.getLeadingTriviaWidth();
    const startPosition = sourceFile.getLineAndCharacterOfPosition(node.pos + leadingTriviaWidth);
    const endPosition = sourceFile.getLineAndCharacterOfPosition(endNode ? endNode.pos : node.end);

    let typeName = INCOMPLETE_TYPENAME;
    let longTypeName = INCOMPLETE_TYPENAME;

    if(type !== INCOMPLETE_TYPE) {
        typeName = getShortTypeName(typeChecker, type, node.parent);
        longTypeName = getLongTypeName(typeChecker, type, node.parent);
    }

    const textBefore = wrap ? '(' : '';
    const textAfter = (wrap ? ')' : '') + ': ' + typeName;
    let hoverMessage = undefined;
    if (longTypeName !== typeName && hover) {
        hoverMessage = new vscode.MarkdownString();
        hoverMessage.appendCodeblock(longTypeName, "typescript");
    }
    const isWarning = configuration.features.highlightAny && /\bany\b/.test(typeName);
    const isIncomplete = typeName === INCOMPLETE_TYPENAME || longTypeName === INCOMPLETE_TYPENAME;

    return { textBefore, textAfter, hoverMessage, startPosition, endPosition, isWarning, isIncomplete };
}

function notifyDocumentChange(
    context: ServiceContext,
    fileName: string,
    textChanges: ReadonlyArray<TextChange>
): void {
    const cachedSourceFile = context.sourceFilesCache.get(fileName);
    if (!cachedSourceFile) {
        logError(`Failed to find cached source file for '${fileName}'.`);
        return;
    }

    try {
        const newSourceFile = textChanges.reduce(updateSourceFile, cachedSourceFile);
        if (newSourceFile !== cachedSourceFile) {
            context.sourceFilesCache.set(fileName, newSourceFile);
            context.updateProgram();
        }
    } catch(e) {
        logError(e.message);
        context.sourceFilesCache.delete(fileName);
        context.updateProgram();
    }
}

function notifyFileChange(
    context: ServiceContext,
    fileName: string,
    fileChangeType: FileChangeType
): void {
    switch (fileChangeType) {
        case FileChangeTypes.Created:
            const isNewRootFile = getParsedCommandLine(context.rootPath).fileNames.some(rootFile => rootFile === fileName);
            if (isNewRootFile) {
                context.updateProgram();
            }
            break;
        
        case FileChangeTypes.Deleted:
            const wasSourceFile = context.getRootFileNames().some(rootFile => rootFile === fileName);
            if (wasSourceFile) {
                context.sourceFilesCache.delete(fileName);
                context.updateProgram();
            }
            break;

        case FileChangeTypes.Changed:
            const isSourceFile = context.getRootFileNames().some(rootFile => rootFile === fileName);
            if (isSourceFile) {
                updateCachedSourceFile(context, fileName);
            }
            break;

        default:
            throw assertNever(fileChangeType);
    }
}

function updateCachedSourceFile(
    context: ServiceContext,
    fileName: string
): void {
    const cachedSourceFile = context.sourceFilesCache.get(fileName);
    if (!cachedSourceFile) {
        return context.updateProgram();
    }

    const fileContent = ts.sys.readFile(fileName, context.getProgram().getCompilerOptions().charset);
    if (fileContent === undefined) {
        logError(`Failed to read file content for '${fileName}'.`);
        return;
    }

    if (fileContent === cachedSourceFile.text) {
        return;
    }

    const newSourceFile = cachedSourceFile.update(fileContent, {
        newLength: fileContent.length,
        span: { start: 0, length: cachedSourceFile.text.length }
    });
    context.sourceFilesCache.set(fileName, newSourceFile);
    return context.updateProgram();
}

function getSourceFile(
    fileName: string,
    languageVersion: ts.ScriptTarget,
    shouldCreateNewSourceFile: boolean | undefined,
    options: ts.CompilerOptions,
    committedSourceFilesCache: Map<string, ts.SourceFile>,
    sourceFilesCache: Map<string, ts.SourceFile>
): ts.SourceFile | undefined {
    if (fileName === ts.getDefaultLibFileName(options)) {
        fileName = ts.getDefaultLibFilePath(options);
    }

    const cachedSourceFile = shouldCreateNewSourceFile ? undefined : committedSourceFilesCache.get(fileName);
    if (cachedSourceFile) {
        return cachedSourceFile;
    }

    const fileContent = ts.sys.readFile(fileName, options.charset);
    if (fileContent === undefined) {
        logError(`Failed to read file content for '${fileName}'.`);
        return undefined;
    }

    const sourceFile = ts.createSourceFile(fileName, fileContent, languageVersion);
    committedSourceFilesCache.set(fileName, sourceFile);
    sourceFilesCache.set(fileName, sourceFile);
    return sourceFile;
}

function createCompilerHost(options: ts.CompilerOptions, committedSourceFilesCache: Map<string, ts.SourceFile>, sourceFilesCache: Map<string, ts.SourceFile>): ts.CompilerHost {
    const defaultCompilerHost = ts.createCompilerHost(options);
    return {
        ...defaultCompilerHost,
        getSourceFile: (fileName, languageVersion, _, shouldCreateNewSourceFile) =>
            getSourceFile(fileName, languageVersion, shouldCreateNewSourceFile, options, committedSourceFilesCache, sourceFilesCache)
    };
}

function getParsedCommandLine(rootPath: string): ts.ParsedCommandLine {
    const configPath = joinPath(rootPath, 'tsconfig.json');
    const configContent = ts.sys.readFile(configPath);
    if (!configContent) {
        throw throwError(`Failed to read config file.`);
    }

    const configJsonFile = ts.parseJsonText(configPath, configContent);
    const parsedConfig = ts.parseJsonSourceFileConfigFileContent(configJsonFile, ts.sys, rootPath, { noEmit: true });
    if (!isUndefined(parsedConfig.errors) && parsedConfig.errors.length > 0) {
        throw throwError(`Failed to parse config file.`);
    }

    return parsedConfig;
}

function getOffsetInSourceFile(sourceFile: ts.SourceFile, position: Position): number {
    return sourceFile.getPositionOfLineAndCharacter(
        position.line,
        position.character);
}

function updateSourceFile(sourceFile: ts.SourceFile, textChange: TextChange) {
    const currentSource = sourceFile.getFullText();
    const updateStartPosition = getOffsetInSourceFile(sourceFile, textChange.start);
    const updateEndPosition = getOffsetInSourceFile(sourceFile, textChange.end);
    const oldSourceBeforeChange = currentSource.slice(0, updateStartPosition);
    const oldSourceAfterChange = currentSource.slice(updateEndPosition);
    const newSource = oldSourceBeforeChange + textChange.newText + oldSourceAfterChange;
    const textChangeRange: ts.TextChangeRange = {
        span: {
            start: updateStartPosition,
            length: updateEndPosition - updateStartPosition
        },
        newLength: textChange.newText.length
    };
    return sourceFile.update(newSource, textChangeRange);
}
