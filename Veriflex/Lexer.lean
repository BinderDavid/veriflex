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

def max_pref {tok : Type}(input : List Char) (rules : List (Rule tok)) : Option (tok × Nat × List Char) :=
  let max_prefixes : List (Rule tok × Option (List Char × List Char)) := rules.map (λ rule => ⟨rule, max_pref_one rule.re input⟩)
  let max_prefixes : List (Option (tok × Nat × List Char)) := max_prefixes.map apply_rule
  let max_prefixes : List (tok × Nat × List Char) := max_prefixes.filterMap id
  let result : Option (tok × Nat × List Char):= find_first_max max_prefixes (λ x => x.2.1)
  result

theorem max_pref_length :
  max_pref input rules = some ⟨tok,n,rest⟩ →
  input.length = n + rest.length := by
  unfold max_pref
  simp!
  generalize H_eq : List.filterMap (apply_rule ∘ fun rule => (rule, max_pref_one rule.re input)) rules = xs
  have H_forall : ∀ x ∈ xs, input.length = x.snd.fst + x.snd.snd.length := by
    intros x H_in
    rw [←H_eq] at H_in
    let ⟨tok,n,rest⟩ := x
    simp!
    clear H_eq
    have X := List.mem_filterMap.mp H_in
    let ⟨rule,_,X⟩ := X
    simp! at X
    generalize H_eq : max_pref_one rule.re input = res at X
    cases res with
    | none => simp! at X
    | some val =>
      let ⟨pre,rest'⟩ := val
      simp! at X
      have Y := max_pref_one_prefix H_eq
      let ⟨_,X₁,X₂⟩ := X
      rw [←X₁, ←Y, X₂]
      rw [List.length_append]
  intros H
  have H_in := find_first_max_contained H
  specialize H_forall ⟨ tok,n ,rest⟩ H_in
  assumption

def first_token {tok : Type}(input : List Char) (rules : List (Rule tok)) : Option (tok × List Char) :=
  match max_pref input rules with
  | none => none
  | some ⟨tok,n,rest⟩ => if n > 0
                         then some ⟨tok, rest⟩
                         else none



theorem first_token_smaller :
  first_token input rules = some ⟨tok, rest⟩ →
  rest.length < input.length := by
  unfold first_token
  generalize H_eq : max_pref input rules = res
  intros H
  cases res with
  | none =>
    simp! at H
  | some v =>
    let ⟨token,n,rest'⟩ := v
    simp! at H
    have X : input.length = n + rest'.length := by
      apply max_pref_length
      apply H_eq
    let ⟨H₁,_,H₂⟩ := H
    rw [X,H₂]
    omega

def measure (x : Option (tok × List Char)) : Nat :=
  match x with
  | none => 0
  | some ⟨ _, xs ⟩ => xs.length + 1

def lex_rec {tok : Type}(input : List Char)(foo: Option (tok × List Char))(rules : List (Rule tok)) : List tok × List Char :=
  match foo with
  | none => ([], input)
  | some (tok, rest) =>
    let (toks, rest') :=
      lex_rec rest (first_token rest rules) rules
    (tok :: toks, rest')
termination_by measure foo
decreasing_by
  simp!
  generalize H : first_token rest rules = x
  cases x with
  | none =>
    simp!
  | some x =>
    let ⟨_, x ⟩ := x
    simp!
    exact (first_token_smaller H)

def lex {tok : Type}(input : List Char) (rules : List (Rule tok)) : List tok × List Char :=
  lex_rec input (first_token input rules) rules

end Veriflex
