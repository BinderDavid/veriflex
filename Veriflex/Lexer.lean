import Veriflex.Grammar
import Veriflex.Brzozowski
import Veriflex.Utils
import Veriflex.MaxPrefix

/-!
# Lexer

This file implements the function `lex` which takes a grammar and lexes a string.
-/
namespace Veriflex

def apply_rule  {tok : Type} :
  Rule tok × Option (List Char × List Char) →
  Option (tok × Nat × List Char) := λ ⟨rule,x ⟩ =>
  match x with
  | none => none
  | some ⟨pre, rest⟩ => some ⟨rule.action (String.mk pre), pre.length, rest⟩

def max_pref {tok : Type}(input : List Char) (rules : List (Rule tok)) : Option (tok × List Char) :=
  let max_prefixes : List (Rule tok × Option (List Char × List Char)) := rules.map (λ rule => ⟨rule, max_pref_one rule.re input⟩)
  let max_prefixes : List (Option (tok × Nat × List Char)) := max_prefixes.map apply_rule
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
