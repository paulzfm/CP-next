{ name = "cp-next"
, dependencies =
  [ "aff"
  , "ansi"
  , "arrays"
  , "bifunctors"
  , "console"
  , "control"
  , "datetime"
  , "effect"
  , "either"
  , "exceptions"
  , "foldable-traversable"
  , "free"
  , "identity"
  , "lists"
  , "math"
  , "maybe"
  , "newtype"
  , "node-buffer"
  , "node-fs"
  , "node-fs-aff"
  , "node-path"
  , "node-readline"
  , "now"
  , "ordered-collections"
  , "parsing"
  , "partial"
  , "prelude"
  , "spec"
  , "strings"
  , "transformers"
  , "tuples"
  , "unicode"
  , "stringutils"
  , "refs"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
