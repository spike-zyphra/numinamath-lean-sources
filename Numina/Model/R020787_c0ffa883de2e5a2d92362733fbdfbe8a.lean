import Mathlib

open Real

lemma lemma_1 (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    x - x * sqrt y / (x + y) ≥ 1 / 2 := by
  have h1 : 0 ≤ x + y := by nlinarith
  have h2 : 1 ≤ sqrt y := by
    have h3 : 1 ≤ y := hy
    have h4 : sqrt 1 ≤ sqrt y := Real.sqrt_le_sqrt (by linarith)
    have h5 : sqrt 1 = 1 := Real.sqrt_one
    linarith
  have h3 : x - x * sqrt y / (x + y) = (x * (x + y) - x * sqrt y) / (x + y) := by
    field_simp
    <;> ring
  rw [h3] at *
  have h4 : x * (x + y) - x * sqrt y ≥ (1 / 2) * (x + y) := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (sqrt y - 1), sq_nonneg (x - sqrt y),
      sq_nonneg (x + y - 2 * sqrt y), sq_nonneg (x - 1), sq_nonneg (sqrt y - 1),
      Real.sqrt_nonneg y, Real.sq_sqrt (show 0 ≤ y by linarith),
      mul_nonneg (show (0:ℝ) ≤ x by linarith) (show (0:ℝ) ≤ sqrt y by positivity),
      mul_nonneg (show (0:ℝ) ≤ x - 1 by linarith) (show (0:ℝ) ≤ y - 1 by linarith)]
  have h5 : (x * (x + y) - x * sqrt y) / (x + y) ≥ 1 / 2 := by
    have h6 : 0 < x + y := by
      nlinarith
    apply (le_div_iff₀ h6).mpr
    linarith
  exact h5


theorem inequalities_113723 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    a * sqrt b / (a + b) + b * sqrt c / (b + c) + c * sqrt a / (c + a) + 3 / 2 ≤ a + b + c := by
  have h1 : a - a * sqrt b / (a + b) ≥ 1 / 2 := by
    apply lemma_1
    all_goals linarith
  have h2 : b - b * sqrt c / (b + c) ≥ 1 / 2 := by
    apply lemma_1
    all_goals linarith
  have h3 : c - c * sqrt a / (c + a) ≥ 1 / 2 := by
    apply lemma_1
    all_goals linarith
  linarith