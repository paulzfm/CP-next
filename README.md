# CP - The Next Generation

This repository is a fork of [Next-CP](https://github.com/yzyzsun/CP-next), a *compositional* programming language, founded on a core calculus named *Fi+*.
I am now actively adding new experimental features to it.

## Build

If you want to run CP programs locally using a CLI, you can follow the procedure below:

- First of all, you need to install [Node.js](https://nodejs.org).
- Then execute `npm install` to get all of the dev dependencies.
- After installation, you can choose either of the following npm scripts:
  - `npm start` to run a REPL;
  - `npm test` to run a test suite checking `examples/*.cp`.

## New Features

- [x] REPL: store defined/imported bindings in the REPL context
- [x] REPL: auto-completer
- [ ] REPL: load history from file
- [ ] Type system: nominal typing
