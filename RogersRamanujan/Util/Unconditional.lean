module

import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint.Misc
public meta import Lean.Elab.Command

/-! # Unconditional string parser

The parser `unconditional` accepts a string and creates a parser that will parse that string
unconditionally, even if it is part of an identifier. Use with caution. Make sure that its usecases
will not conflict with possible identifiers, and document it clearly.

Due to knowledge limitations of the author, I had initially hoped for the following usage:
```lean
syntax num unconditional("φ") num : term
```

But we will have to settle for:
```lean
declare_unconditional_syntax testPhi := "φ"
syntax num testPhi num : term
```

See `RogersRamanujan/TacticTest/Unconditional.lean` for the test.
-/

@[expose] public meta section

open Lean Parser PrettyPrinter

/-- Parser function that matches an exact string at the current position,
regardless of whether it appears in the middle of an identifier. -/
partial def unconditionalFn (s : String) : ParserFn := fun c state ↦
  let start := state.pos
  let sEnd := s.rawEndPos
  let rec /-- Loop body of `unconditionalFn`. -/ go (sPos iPos : String.Pos.Raw) : ParserState :=
    if sPos >= sEnd then
      let state := { state with pos := iPos }
      let state := whitespace c state
      state.pushSyntax <| .atom (.original
        (c.substring start start) start
        (c.substring iPos state.pos) iPos) s
    else if c.atEnd iPos then
      state.mkError s!"{s} expected"
    else
      let expected := sPos.get s
      if c.get iPos == expected then
        go (sPos + expected) (c.next iPos)
      else
        state.mkError s!"{s} expected"
  go 0 start

@[nolint docBlame]
def unconditional (kind : Name) (s : String) : Parser :=
  let tokens := ["$", s]
  let antiquotP := mkAntiquot kind.toString kind (isPseudoKind := true)
  node `unconditional {
    fn := withAntiquotFn antiquotP.fn (unconditionalFn s) true
    info.firstTokens := .tokens tokens
    info.collectTokens := (tokens ++ ·) }

open Elab Command

/-- Make a new parser for unconditionally matching a string. Use with caution. -/
elab "declare_unconditional_syntax" id:ident " := " s:str : command => do
  have root_id : Name := (`_root_).append id.getId
  let parenthesizer_id ← liftCoreM <| mkFreshUserName id.getId
  let formatter_id ← liftCoreM <| mkFreshUserName id.getId
  elabCommand <| ← `(command|
@[nolint docBlame]
public meta def $(mkIdent root_id) := unconditional $(quote id.getId) $(quote s.getString))
  elabCommand <| ← `(command|
@[combinator_parenthesizer $id]
public meta def $(mkCIdent parenthesizer_id) : Parenthesizer :=
  Parenthesizer.node.parenthesizer `unconditional .visitToken)
  elabCommand <| ← `(command|
@[combinator_formatter $id]
public meta def $(mkCIdent formatter_id) : Formatter :=
  Formatter.node.formatter `unconditional (Formatter.visitAtom Name.anonymous))
