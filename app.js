import { basicSetup } from '@codemirror/basic-setup';
import { Compartment, EditorState } from '@codemirror/state';
import { EditorView, keymap } from '@codemirror/view';
import { defaultTabBinding } from '@codemirror/commands';
import { LanguageSupport, LezerLanguage, continuedIndent, foldNodeProp, indentNodeProp } from '@codemirror/language';
import { styleTags, tags as t } from '@codemirror/highlight';
import { parser } from './zord';

const zordLanguage = LezerLanguage.define({
  parser: parser.configure({
    props: [
      indentNodeProp.add({
        RecordType: continuedIndent(),
        Record: continuedIndent(),
      }),
      foldNodeProp.add({
        RecordType(tree) { return { from: tree.from + 1, to: tree.to - 1 } },
        Record(tree)     { return { from: tree.from + 1, to: tree.to - 1 } },
        Document(tree)   { return { from: tree.from + 1, to: tree.to - 1 } },
      }),
      styleTags({
        'type extends let letrec trait implements inherits': t.definitionKeyword,
        'if then else new open in toString forall Int Double Bool String Top Bot Trait': t.keyword,
        'override': t.modifier,
        'true false undefined': t.atom,
        Unit: t.unit,
        TermName: t.variableName,
        TermNameDecl: t.definition(t.variableName),
        Label: t.propertyName,
        LabelDecl: t.definition(t.propertyName),
        LineComment: t.lineComment,
        BlockComment: t.blockComment,
        Number: t.number,
        String: t.string,
        Document: t.docString,
        TypeOp: t.typeOperator,
        ArithOp: t.arithmeticOperator,
        LogicOp: t.logicOperator,
        CompareOp: t.compareOperator,
        MergeOp: t.operator,
        TraitArrow: t.definition(t.punctuation),
        '( )': t.paren,
        '{ }': t.brace,
        '[ ]': t.squareBracket,
        '< >': t.angleBracket,
        '.': t.derefOperator,
        ';': t.separator,
      }),
    ],
  }),
  languageData: {
    closeBrackets: { brackets: ['{', '(', '[', '"', '`'] },
    commentTokens: { line: '--', block: { open: '{-', close: '-}' } },
  },
});

export const language = new Compartment;
export const languageSupport = new LanguageSupport(zordLanguage);

export function editorState(doc, binding) {
  return EditorState.create({
    doc,
    extensions: [
      basicSetup,
      EditorView.lineWrapping,
      EditorState.tabSize.of(2),
      keymap.of([defaultTabBinding, { key: 'Mod-Enter', run: binding }]),
      language.of([]),
    ],
  });
}

export function editorView(state, parent) {
  return new EditorView({ state, parent });
}

export { default as Zord } from './src/Zord.purs';
