import Veriflex.Grammar
import Veriflex.Brzozowski
import Veriflex.Utils

/-!
# Lexer

This file implements the function `lex` which takes a grammar and lexes a string.
-/
namespace Veriflex

def maxpref_one_rec (best : Option (List Char × List Char))
        (left right : List Char)
        (re : RE)
        : Option (List Char × List Char) :=
  match right with
  | [] => if nullable re
          then some (left, right)
          else best
  | s :: right' => let re' := derivative s re
               let left' := left ++ [s]
               if nullable re'
               then maxpref_one_rec (some (left', right')) left' right' re'
               else maxpref_one_rec best left' right' re'


/--
Given a string and a rule, compute the longest prefix that matches this rule.
If the regular expression matches successfully, return the computed token,
the length of the consumed input, and the remainder of the output.
-/
def maxpref_one {tok : Type}(s : List Char) (r : Rule tok) : Option (tok × Nat × List Char) :=
  match maxpref_one_rec none [] s r.re with
  | none => none
  | some (pre, rest) => some (r.action (String.mk pre), pre.length, rest)


theorem max_pref_one_smaller :
  maxpref_one input rule = some ⟨tok, n, rest⟩ →
  rest.length < input.length := sorry

def max_pref {tok : Type}(input : List Char) (rules : List (Rule tok)) : Option (tok × List Char) :=
  let max_prefixes : List (Option (tok × Nat × List Char)) := rules.map (λ rule => maxpref_one input rule)
  let max_prefixes : List (tok × Nat × List Char) := max_prefixes.filterMap id
  let result : Option (tok × Nat × List Char):= find_first_max max_prefixes (λ x => x.2.1)
  result.map (λ x => ⟨x.1, x.2.2 ⟩)

theorem max_pref_smaller :
  max_pref input rules = some ⟨tok, rest ⟩ →
  rest.length < input.length := by
  sorry


def measure (x : Option (tok × List Char)) : Nat :=
  match x with
  | none => 0
  | some ⟨ _, xs ⟩ => xs.length + 1


def lex_rec {tok : Type}(input : List Char)(foo: Option (tok × List Char))(rules : List (Rule tok)) : List tok × List Char :=
  match foo with
  | none => ([], input)
  | some (tok, rest) =>
    let (toks, rest') :=
      lex_rec rest (max_pref rest rules) rules
    (tok :: toks, rest')
termination_by measure foo
decreasing_by
  simp!
  generalize H : max_pref rest rules = x
  cases x with
  | none =>
    simp!
  | some x =>
    let ⟨_, x ⟩ := x
    simp!
    apply max_pref_smaller
    exact H

def lex {tok : Type}(input : List Char) (rules : List (Rule tok)) : List tok × List Char :=
  lex_rec input (max_pref input rules) rules


end Veriflex
