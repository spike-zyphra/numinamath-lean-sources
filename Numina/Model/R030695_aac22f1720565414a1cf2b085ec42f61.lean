import Mathlib

theorem algebra_111794 :
    ∃ f : ℕ → ℤ,
      (∀ i, f i > 0) ∧
      (∀ i, Odd i → i ≥ 2 → f i = (f (i - 2) + f (i - 1)) / 2) ∧
      (∀ i, Even i → f i = √(f (i - 1) * f (i + 1))) := by
  use fun _ => (2 : ℤ)
  constructor
  · -- Show that all elements are positive
    intro i
    norm_num
  constructor
  · -- Show the arithmetic mean condition for odd indices i ≥ 2
    intro i hi1 hi2
    simp at *
  · -- Show the geometric mean condition for even indices
    intro i hi
    simp [Int.sqrt] at *