# CP - The Next Generation

CP is a *compositional* programming language, founded on a core calculus named *Fi+*. The next-gen CP is shipped with more features and implemented in [PureScript](https://www.purescript.org) (a Haskell-like language that compiles to JavaScript).

## Language Features

- A typed lambda calculus with six base types (`Int` `Double` `String` `Bool` `Top` `Bot`), built-in arrays (`[1; 2; 3] : [Int]`), and some built-in operations over them;
- A merge operator [^Merge], disjoint intersection types [^λi] and disjoint polymorphism [^Fi];
- Nested composition and distributive subtyping [^NeColus];
- Compositional Programming [^CP] with first-class traits [^SEDEL];
- Type-directed operational semantics [^TDOS] for *Fi+* with {substitution,closure,HOAS}-based {big,small}-step variants;
- An embedded DSL for document authoring called ExT [^ExT].

[^Merge]: Jana Dunfield. [Elaborating Intersection and Union Types](https://research.cs.queensu.ca/home/jana/papers/intcomp-jfp/Dunfield14_elaboration.pdf). In *JFP 2014*.  
[^λi]: Bruno C. d. S. Oliveira, Zhiyuan Shi, and João Alpuim. [Disjoint Intersection Types](https://i.cs.hku.hk/~bruno/papers/icfp2016.pdf). In *ICFP 2016*.  
[^Fi]: João Alpuim, Bruno C. d. S. Oliveira, and Zhiyuan Shi. [Disjoint Polymorphism](https://i.cs.hku.hk/~bruno/papers/ESOP2017.pdf). In *ESOP 2017*.  
[^SEDEL]: Xuan Bi and Bruno C. d. S. Oliveira. [Typed First-Class Traits](https://i.cs.hku.hk/~bruno/papers/traits.pdf). In *ECOOP 2018*.  
[^NeColus]: Xuan Bi, Bruno C. d. S. Oliveira, and Tom Schrijvers. [The Essence of Nested Composition](https://i.cs.hku.hk/~bruno/papers/nested.pdf). In *ECOOP 2018*.  
[^Fi+]: Xuan Bi, Ningning Xie, Bruno C. d. S. Oliveira and Tom Schrijvers. [Distributive Disjoint Polymorphism for Compositional Programming](https://i.cs.hku.hk/~bruno/papers/esop2019.pdf). In *ESOP 2019*.  
[^CP]: Weixin Zhang, Yaozhu Sun, and Bruno C. d. S. Oliveira. [Compositional Programming](https://i.cs.hku.hk/~bruno/papers/toplas2021.pdf). In *TOPLAS 2021*.  
[^TDOS]: Xuejing Huang, Jinxu Zhao, and Bruno C. d. S. Oliveira. [Taming the Merge Operator](https://i.cs.hku.hk/~bruno/papers/jfp2021.pdf). In *JFP 2021*.  
[^ExT]: Yaozhu Sun, Utkarsh Dhandhania, and Bruno C. d. S. Oliveira. [Compositional Embeddings of Domain-Specific Languages](). *Unpublished*.  

## Online Demo

[PLGround](https://plground.org) provides an online CP interpreter and a wiki-like document repository. Documents are written in ExT and rendered in your web browser.

Since the frontend code uses the Fetch API, PLGround is expected to work on Chrome 42+, Firefox 39+, Edge 14+, Safari 10.1+, or other modern browsers.

## CLI Setup

If you want to run CP programs locally using a CLI, you can follow the procedure below:

- First of all, you need to install [Node.js](https://nodejs.org).
- Then execute `npm install` to get all of the dev dependencies.
- After installation, you can choose either of the following npm scripts:
  - `npm start` to run a REPL;
  - `npm test` to run a test suite checking `examples/*.cp`.

If you want to start a PLGround server locally, take the first two steps above and then:

- Install [Ruby](https://www.ruby-lang.org).
- Execute `bundle install` to get [Ruby on Rails](https://rubyonrails.org) and other gems.
- Execute `npm run build` if you have modified PureScript code, grammar files, or `app.js` (i.e. every file that `backend/app/assets/javascripts/bundle.js` depends on).
- Execute `npm run server` to start a web server.

## REPL Example

```
$ npm start
......
Next-Gen CP REPL, version x.x.x

> :load examples/bench.cp
7773
<BigStep mode: 1.024s>

> :mode StepTrace

> 1+2*3
(1 + (2 * 3))
......
(1 + 6)
↓ Step-BinaryV
7
<StepTrace mode: 0.021s>
```

## Grammar Maintenance

There are currently four different copies of the CP grammar. If you want to modify the grammar, please remember to change them all:

1. PureScript parser based on parser combinators, used in REPL ([see the code here](./src/CP/Parser.purs)).
2. ANTLR-generated LL(*) parser, used in PLGround ([see this directory](./antlr/)).
3. Lezer-generated incremental parser for the CodeMirror 6 code editor ([see the grammar file](./lezer.grammar)).
4. TextMate grammar specification for VS Code, mainly keyword highlighting ([see the JSON file](./vscode/CP.tmLanguage.json)).

## VS Code Extension

CP language support can be found on [VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=yzyzsun.cp-next).

If you want to build it from scratch, please execute `npm run vscode`. Then a `.vsix` file will be generated in `vscode/`.

## Next-Gen CP versus Original CP

The original CP (hereinafter CP1) is introduced and formalized in our TOPLAS paper *Compositional Programming*. Its reference implementation is included in the [artifact](https://github.com/wxzh/CP). The next-gen CP (hereinafter CP2) polishes the syntax of CP1 and extends it with new features, but their semantics are essentially the same. CP2 has a brand-new implementation that supersedes the original one.

Concerning implementation languages, CP1 is written in Haskell, while CP2 is written in PureScript. Thus, CP2 can easily run in a web browser without losing the ability to run traditionally in a terminal. Concerning the semantics of the core calculus *Fi+*, it is further elaborated to *F-co* in CP1 but has direct operational semantics in CP2. Furthermore, new features recently added and some syntactic differences can be found at [CHANGELOG.md](CHANGELOG.md).
