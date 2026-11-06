import Mathlib

open Real

theorem algebra_283861 (x : ℝ) (hx : x > 0) :
    sqrt (2 * (1 + sqrt (1 + ((x ^ 4 - 1) / (2 * x ^ 2)) ^ 2))) = (x ^ 2 + 1) / x := by
  have h1 : 1 + ((x ^ 4 - 1) / (2 * x ^ 2)) ^ 2 = ( (x ^ 2 / 2) + (1 / (2 * x ^ 2)) ) ^ 2 := by
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring
  have h2 : sqrt (1 + ((x ^ 4 - 1) / (2 * x ^ 2)) ^ 2) = (x ^ 2 / 2) + (1 / (2 * x ^ 2)) := by
    rw [h1]
    have h_pos : (x ^ 2 / 2) + (1 / (2 * x ^ 2)) ≥ 0 := by
      apply add_nonneg
      · -- x^2 >= 0
        apply div_nonneg
        · nlinarith [hx]
        · nlinarith [hx]
      · -- 1/(2*x^2) >= 0
        apply div_nonneg
        · norm_num
        · positivity
    rw [Real.sqrt_sq h_pos]
  have h3 : 2 * (1 + sqrt (1 + ((x ^ 4 - 1) / (2 * x ^ 2)) ^ 2)) = (x + 1 / x) ^ 2 := by
    rw [h2]
    field_simp
    ring_nf
  rw [h3]
  have h_pos : (x + 1 / x) ≥ 0 := by
    apply add_nonneg
    · -- x >= 0
      positivity
    · -- 1/x >= 0
      positivity
  rw [Real.sqrt_sq h_pos]
  field_simp
  all_goals nlinarith