import Mathlib

open Real

theorem inequalities_218505 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b ≤ 2) :
    1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) ≤ 2 / (1 + a * b) := by
  have h1 : 0 ≤ a * b := mul_nonneg ha hb
  have h2 : 0 < 1 + a * b := by
    nlinarith [mul_nonneg ha hb]
  have h3 : 0 < 1 + a ^ 2 := by
    nlinarith [sq_nonneg a]
  have h4 : 0 < 1 + b ^ 2 := by
    nlinarith [sq_nonneg b]
  have h5 : 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) - 2 / (1 + a * b) ≤ 0 := by
    have h6 : (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) - 2 / (1 + a * b)) =
        (( (1 + b ^ 2) * (1 + a * b) + (1 + a ^ 2) * (1 + a * b) - 2 * (1 + a ^ 2) * (1 + b ^ 2) )) / (( (1 + a ^ 2) * (1 + b ^ 2) * (1 + a * b) )) := by
      field_simp
      <;> ring
    rw [h6] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show numerator is non-positive
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), 
                sq_nonneg (a * b - 1), sq_nonneg (a + b - 2), mul_nonneg ha hb, 
                mul_nonneg (sub_nonneg.mpr (by linarith : b ≤ 2 - a)) (show 0 ≤ a by linarith)]
    all_goals
      positivity
  linarith