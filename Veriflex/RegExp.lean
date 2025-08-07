/-!
# Regular Expressions and Matching

This file defines regular expressions and the inductive matching relation which characterizes when a string matches against a regular expression.
-/

namespace Veriflex

inductive NotNullable : (Char → Bool) → Prop where
  | Ex : (f : Char → Bool) (c : Char) → (f c = true) → NotNullable f

/-- Regular Expressions -/
inductive RE : Type where
    /--
    The regular expression corresponding to the empty language:

    `L(Empty) = ∅`
    -/
  | Empty
    /--
    The regular expression matching an empty string:

    `L(Epsilon) = {""} `
    -/
  | Epsilon
    /-- Kleene star: Zero or more repetitions -/
  | Star : RE → RE
    /-- One or more repetitions -/
  | Plus : RE → RE
    /--
    Choice between two alternatives:

    `L(Union(re₁, re₂) = L(re₁) ∪ L(re₂)`
    -/
  | Union : RE → RE → RE
    /--
    Concatenation of two words:

    `L(App(re₁,re₂)) = { w₁w₂ | w₁ ∈ L(re₁), w₂ ∈ L(re₂) }`
    -/
  | App : RE → RE → RE
    /--
    The regular expression matching the corresponding symbol:

    `L(Symbol('a')) = { "a" }`
    -/
  | Symbol : Char → RE
    /--
    The regular expression matching every character for which
    the given property holds. We enforce that the property cannot
    be false for every argument, so `L(Property(P)) ≠ ∅`.

    `L(Property(P)) = { a | a ∈ Σ ∧ P(a) = true }`
    -/
  | Property : (f : Char → Bool) → NotNullable f →  RE

/--
A helper function which computes the union of a list of regular expressions.
-/
def unions (res: List RE) : RE :=
  match res with
   | [] => RE.Empty
   | (re :: res) => RE.Union re (unions res)

/--
A helper function which computes the regular expression which appends all elements of a list of regular expressions.
-/
def apps (res : List RE) : RE :=
  match res with
   | [] => RE.Epsilon
   | (re :: res) => RE.App re (apps res)

/--
A helper function which computes the regular expression which matches exactly the given string.
-/
def from_string (l : List Char) : RE :=
  apps (List.map (λ c => RE.Symbol c) l)

/--
The `Matching` relation describes when a regular expression matches a list of characters.
-/
inductive Matching : RE → List Char → Prop where
    /-- `Epsilon` matches against the empty string. -/
  | EPSILON :
    Matching RE.Epsilon []
    /-- `Plus` matches at least once. -/
  | PLUS : ∀ w₁ w₂,
    Matching re w₁ →
    Matching (RE.Star re) w₂ →
    Matching (RE.Plus re) (w₁ ++ w₂)
    /-- `Star` matches the empty string. -/
  | STAR_0 :
    Matching (RE.Star re) []
    /-- `Star` matches more than once. -/
  | STAR_N : ∀ w₁ w₂,
    Matching re w₁ →
    Matching (RE.Star re) w₂ →
    Matching (RE.Star re) (w₁ ++ w₂)
    /-- `Union` matches if the left side matches -/
  | UNION_L :
    Matching re₁ w →
    Matching (RE.Union re₁ re₂) w
    /-- `Union` matches if the right side matches -/
  | UNION_R :
    Matching re₂ w →
    Matching (RE.Union re₁ re₂) w
    /-- `App` matches the concatenation of two strings. -/
  | APP : ∀ w₁ w₂,
    Matching re₁ w₁ →
    Matching re₂ w₂ →
    Matching (RE.App re₁ re₂) (w₁ ++ w₂)
    /-- `Symbol` matches the specified symbol. -/
  | SYMBOL :
    Matching (RE.Symbol c) [c]
  | PROPERTY : ∀ c P H,
    P c = true →
    Matching (RE.Property P H) [c]

end Veriflex
