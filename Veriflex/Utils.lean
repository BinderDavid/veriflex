/-!
# Utility functions

This file contains generic utility functions
-/

def find_first_max_rec {α : Type} : Option α → List α → (α → Nat) → Option α := λ best l f =>
  match l with
  | List.nil => best
  | List.cons x xs =>
    match best with
    | none => find_first_max_rec (some x) xs f
    | some b => if f b < f x
                then find_first_max_rec (some x) xs f
                else find_first_max_rec (some b) xs f

def find_first_max {α : Type} : List α → (α → Nat) → Option α := λ l f =>
  find_first_max_rec none l f

theorem find_first_max_empty :
  find_first_max l f = none ↔ l = [] := sorry

theorem find_first_max_contained :
  find_first_max l f = some x → x ∈ l := sorry

-- TODO: Theorems about maximality.
