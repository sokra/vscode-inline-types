import * as vscode from "vscode";

export interface Position {
    readonly line: number;
    readonly character: number;
}

export interface Decoration {
    readonly textBefore: string;
    readonly textAfter: string;
    readonly hoverMessage?: vscode.MarkdownString | vscode.MarkdownString[];
    readonly startPosition: Position;
    readonly endPosition: Position;
    readonly isWarning: boolean;
    readonly isIncomplete: boolean;
}

export interface TextChange {
    readonly start: Position;
    readonly end: Position;
    readonly newText: string;
}

export type FileChangeType = 'Created' | 'Changed' | 'Deleted';
export const FileChangeTypes: { readonly [P in FileChangeType]: P } = {
    Created: 'Created',
    Changed: 'Changed',
    Deleted: 'Deleted'
};

export interface Service {
    notifyDocumentChange(fileName: string, textChanges: ReadonlyArray<TextChange>): void;
    notifyFileChange(fileName: string, fileChangeType: FileChangeType): void;
    getDecorations(fileName: string): ReadonlyArray<Decoration>;
    isUpToDate(fileName: string): boolean;
}

export type FeatureType =
    | 'variableType'
    | 'functionVariableType'
    | 'functionReturnType'
    | 'functionParameterType'
    | 'propertyType'
    | 'objectPatternType'
    | 'arrayPatternType'
    | 'objectLiteralType'
    | 'parameterName'
    | 'highlightAny'
    | 'showIncompleteInfo'

export interface Configuration {
    readonly features: { readonly [P in FeatureType]: boolean };
    readonly updateDelay: number;
    readonly compileDelay: number;
    readonly lightThemeDecorationStyle: DecorationStyle;
    readonly darkThemeDecorationStyle: DecorationStyle;
}

export interface DecorationStyle {
    readonly opacity: number;
    readonly color: string;
    readonly warnColor: string;
}

export interface Disposable {
    dispose(): any;
}
