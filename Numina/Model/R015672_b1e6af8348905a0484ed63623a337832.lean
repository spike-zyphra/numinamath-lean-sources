import Mathlib

theorem algebra_148109 (a b c : ℝ) (ha : a < b) (hf : ∀ x, a * x ^ 2 + b * x + c ≥ 0) :
    (a + b + c) / (b - a) ≥ 3 := by
  have h1 : b - a > 0 := by linarith
  have h2 := hf 0
  have h3 := hf 1
  have h4 := hf (-2)
  have h5 := hf 2
  have h6 : 4 * a - 2 * b + c ≥ 0 := by
    nlinarith [h4]
  have h7 : a + b + c ≥ 3 * (b - a) := by
    nlinarith [h4]
  have h8 : (a + b + c) / (b - a) ≥ 3 := by
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  exact h8