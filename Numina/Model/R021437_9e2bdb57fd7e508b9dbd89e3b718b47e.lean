import Mathlib

theorem algebra_252902 (a b c : ℝ) (ha : a ≠ 0) (h : ∀ x, a * x ^ 2 + b * x + c ≥ 0)
    (h1 : a < b) :
    (a + b + c) / (b - a) ≥ 3 := by
  have h2 : a + b + c ≥ 0 := by
    specialize h 1
    nlinarith
  have h4 : 4 * a - 2 * b + c ≥ 0 := by
    specialize h (-2)
    nlinarith
  have h5 : b - a > 0 := by linarith
  have h7 : a + b + c ≥ 3 * (b - a) := by
    nlinarith [h4]
  have h8 : (a + b + c) / (b - a) ≥ 3 := by
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith
  exact h8