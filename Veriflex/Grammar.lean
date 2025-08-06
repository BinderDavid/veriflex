import Veriflex.RegExp
/-!
# Rules and Grammar

This file describes the rules which make up the grammar of the lexer.
Each rule consists of a regular expression and a semantic action, i.e.
a function which takes the lexed string and transforms it into a token.
-/

namespace Veriflex

structure Rule (tok : Type ): Type where
  re : RE
  action : String → tok

def MatchingR {tok : Type}(R : Rule tok) (ls : List Char) : Prop :=
  Matching R.re ls

/-- `p` is a prefix of `z` -/
def Prefix (p z : List Char) : Prop :=
  ∃ s, p ++ s = z

/-- `p` is the longest prefix of `z` matching a rule in the set `R` -/
def MaxPref {tok : Type}(R : List (Rule tok)) (p z : List Char) : Prop :=
  /- `p` is a prefix of  `z`-/
  Prefix p z ∧
  /- `p` matches against a rule in `R`-/
  (∃ r ∈ R, MatchingR r p) ∧
  /- All longer prefixes don't match -/
  (∀ p', Prefix p' z ∧ p.length < p'.length →
         ∀ r' ∈ R, ¬ (MatchingR r' p'))

inductive Index {α : Type } : Nat → α → List α → Prop where
  | ZERO : Index Nat.zero x (x :: xs)
  | SUCC : Index n x xs → Index (Nat.succ n) x (y :: xs)

def FirstToken {tok : Type}(R : List (Rule tok)) (t : tok) (pre z : List Char) : Prop :=
  /- `pre` must not be empty -/
  pre ≠ [] ∧
  /- `pre` must be a maximal prefix of `z` matching a rule in `R` -/
  MaxPref R pre z ∧
  /- There is a rule `r` in `R` which matches `pre` and produces token `tok` -/
  (∃ n r, Index n r R ∧
          MatchingR r pre ∧
          r.action pre.toString = t ∧
          /- All other rules which occur earlier in `R` do not match -/
          (∀ r' n', n' < n → Index n' r' R → ¬ MatchingR r' pre))


inductive Tokens {tok : Type} : List (Rule tok) → List Token →  List Char → List Char → Prop where
  | NIL :
    Tokens R [] xs xs
  | CONS :
    z = pre ++ s →
    FirstToken R t pre z →
    Tokens R  toks u s →
    Tokens R (tok :: toks) u (z ++ ps)

end Veriflex
