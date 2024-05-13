## Changelog

#### 0.12.0.0

- Add support for Lua 5.4's close and const attributes

#### 0.11.0.2

- Update to work with newer packages

#### 0.11.0.1

- Update to work with newer base

#### 0.11.0

- Migrates custom lexer logic to `alex-tools` package
- Floating-point and integers distinguished in Exp type

#### 0.10.0

- Track the end positions of tokens and the AST in addition to the start

#### 0.9.0

- Transition to parsing Text using a simplified alex lexer and happy parser

#### 0.8.0

- We can now parse Unicode strings from UTF-8 encoded files. By default these
  literals are not interpreted, and we have
  `StringLiteral.interpretStringLiteral` for interpretation and
  `StringLiteral.constructStringLiteral` for constructing Lua string literals
  from UTF-8 encoded ByteStrings.

  Main invariant is that if you print a parsed Lua string, it should be printed
  the same way. (including long strings)

- Empty statements(`EmptyStat`) are now printed by pretty printer to avoid
  ambiguous printing. Previously these two statements were printed the same:

  ```lua
  f();(f)()
  f()(f)()
  ```

  But the first line does not have the parse ambiguity(3 function applications
  in one statement or two function application statements).

- Forgotten `Annotated` instance for `Name` implemented.

- Some warnings are fixed for GHC < 7.10.

#### 0.7.1

- Integer division parsing fixed.

#### 0.7.0

- `language-lua` now supports Lua 5.3.
- Some warnings printed with `base >= 4.8` are fixed.

#### 0.6.3.3

- Some bugs related with assignment statement parsing are fixed(#22).
- Wrong error message for expected `==` operator is fixed(#23).

#### 0.6.3.2

- Build fixed for GHC 7.10.

#### 0.6.3.1

- `Build-tools` field is added to Cabal file.

#### 0.6.3

- Fixed some issues with string parsing. (#17)
- Added `named` variant of text parsers to allow specifying source names. (#18)

#### 0.6.2.1

- Missing test files are added to Cabal package.

#### 0.6.2

- `base` dependency is relaxed for GHC 7.10. Note that alex version
  >3.1.4 is required to compile with GHC 7.10.

#### 0.6.1

- `Generic` and `NFData` instances are implemented for syntax trees.

#### 0.6.0

- Fixed a long string literal parsing bug which was causing long strings to
  terminate at wrong points.
- \\z escape characters in strings are now scanned and interpreted correctly.
- This is first version that parses all of Lua 5.2.2 test suite.

#### 0.5.0

- 2-years-old operator parsing bug fixed. Chained/nested operator expressions
  are now properly parsed.

#### 0.4.6

- Language.Lua.Annotated.Lexer module exposed.

#### 0.4.5

- Fixed a bug that made lexer accept invalid escape sequences in strings.
- Strings are now interpreted \-\- string "\\n" is now parsed to Haskell string
  "\\n", instead of "\\\\n".
- Fixed character code parsing.

#### 0.4.4

- Printer now takes operator precedences into account while printing `Binop`
  and `Unop` expressions and prints parenthesis as necessary.
- Printer now does not put line break in `Binop` expressions.

#### 0.4.3

- `Data` and `Typeable` instances are implemented for syntax tree.

#### 0.4.2

- More tweaks in pretty printer.
- Started using 2 spaces for indentation(instead of 4 as before).

#### 0.4.1

- Some tweaks in pretty-printer.

#### 0.4.0

- `Table` and `FunDef` nodes are removed from simplified syntax.

#### 0.3.1

- Fixed incorrectly exported name `exp` in `Language.Lua.Parser` module.

#### 0.3.0

- Added non-annotated syntax to make code-generation easier.

#### 0.2.3

- Minor internal changes.

#### 0.2.2

- Some tweaks in pretty-printer.

#### 0.2.0

- Syntax tree is annotated. All parsers(`parseText`, `parseFile`) annotate
  resulting tree with source positions.
