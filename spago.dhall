{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name =
    "profunctor-traverse"
, dependencies =
    [ "effect", "console", "psci-support", "record", "variant", "profunctor", "typelevel-prelude", "profunctor-extra" ]
, packages =
    ./packages.dhall
, sources =
    [ "src/**/*.purs", "test/**/*.purs" ]
}
