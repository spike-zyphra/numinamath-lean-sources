import Mathlib

theorem number_theory_169285 (a : ℚ → ℤ) :
    ∃ x y, x ≤ y ∧ a x + a y ≤ 2 * a ((x + y) / 2) := by
  use (0 : ℚ), (0 : ℚ)
  constructor
  · norm_num
  · -- Show that a 0 + a 0 ≤ 2 * a 0
    have h : (a (0 : ℚ) : ℤ) + (a (0 : ℚ) : ℤ) ≤ 2 * (a ((0 + 0 : ℚ) / 2) : ℤ) := by 
      have h_eq : a (0 : ℚ) + a (0 : ℚ) = 2 * a ((0 + 0 : ℚ) / 2) := by
        simp
        <;> ring_nf
      linarith [h_eq]
    linarith