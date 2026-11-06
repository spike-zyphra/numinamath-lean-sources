import Mathlib
open Real Set
open scoped BigOperators
theorem algebra_196873 :
  IsLeast {f | ∃ x : Fin 5 → ℝ, (∀ i, 0 ≤ x i) ∧
    -2 * x 0 + x 1 + x 2 = 2 ∧
    x 0 - 2 * x 1 + x 3 = 2 ∧
    x 0 + x 1 + x 4 = 5 ∧
    f = x 1 - x 0} (-3) := by
  constructor
  · -- Show that -3 is in the set.
    use λ i => match i with
      | 0 => (4 : ℝ)
      | 1 => (1 : ℝ)
      | 2 => (9 : ℝ)
      | 3 => (0 : ℝ)
      | 4 => (0 : ℝ)
      | _ => (0 : ℝ)
    constructor
    · intro i
      fin_cases i <;> norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that -3 is the least element in the set.
    intro f hf
    rcases hf with ⟨x, hx1, h1, h2, h3, h4⟩
    have h00 : 0 ≤ x 0 := by apply hx1 0
    have h11 : 0 ≤ x 1 := by apply hx1 1
    have h22 : 0 ≤ x 2 := by apply hx1 2
    have h33 : 0 ≤ x 3 := by apply hx1 3
    have h44 : 0 ≤ x 4 := by apply hx1 4
    linarith
  all_goals linarith