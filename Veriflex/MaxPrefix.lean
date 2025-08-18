import Veriflex.Grammar
import Veriflex.Brzozowski

/-!
# MaxPrefix
-/

namespace Veriflex

def max_pref_one_rec
  (re : RE)
  (best : Option (List Char × List Char))
  (left right : List Char)
 : Option (List Char × List Char) :=
  match right with
  | [] => if nullable re
          then some (left, right)
          else best
  | s :: right' => let re' := derivative s re
               let left' := left ++ [s]
               if nullable re'
               then max_pref_one_rec re' (some (left', right')) left' right'
               else max_pref_one_rec re' best left' right'


theorem max_pref_one_rec_prefix :
  max_pref_one_rec re best left right = some ⟨pre, rest⟩ →
  best = some ⟨pre, rest⟩ ∨ left ++ right = pre ++ rest := by
  intros H
  revert re best left pre rest
  induction right with
  | nil =>
    intros re best left pre rest H
    simp! at H
    by_cases H_nullable : nullable re
    . rw [H_nullable] at H
      simp! at H
      apply Or.inr
      let ⟨H₁,H₂⟩ := H
      rw [H₁,H₂]
    . rw [eq_false_of_ne_true H_nullable] at H
      simp! at H
      apply Or.inl
      assumption
  | cons hd tl IH =>
    intros re best left pre rest H
    simp! at H
    by_cases H_nullable : nullable (derivative hd re)
    . rw [H_nullable] at H
      simp! at H
      specialize IH H
      apply Or.inr
      cases IH with
      | inl IH =>
        cases IH
        simp!
      | inr IH => simp! at * ; assumption
    . rw [eq_false_of_ne_true H_nullable] at H
      simp! at H
      specialize IH H
      cases IH with
      | inl IH => apply Or.inl ; assumption
      | inr IH => apply Or.inr ; simp! at * ; assumption

/--
Given an input string and a rule, compute the longest prefix of the input that matches this rule.
If the regular expression matches successfully, return the computed token,
the length of the consumed input, and the remainder of the output.
-/
def max_pref_one (re : RE)(input : List Char)  : Option (List Char × List Char) :=
  max_pref_one_rec re none [] input

theorem max_pref_one_prefix :
  max_pref_one rule input = some ⟨pre, rest⟩ →
  pre ++ rest = input := by
  unfold max_pref_one
  intros H
  have H' := max_pref_one_rec_prefix H
  cases H' with
  | inl H' => cases H'
  | inr H' => symm ; assumption

theorem max_pref_one_matches :
  max_pref_one rule input = some ⟨pre, rest⟩ →
  Matching re pre := sorry

theorem max_pref_one_longest :
  max_pref_one rule input = some ⟨pre, rest⟩ →
  ∀ pre' rest',
    pre' ++ rest' = input →
    Matching re pre' →
    pre'.length <= pre.length := sorry
