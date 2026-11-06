import Mathlib

theorem algebra_249663 {M : ℝ} (hM : M = (√5 + 2) ^ ((1 : ℝ) / 3) - (√5 - 2) ^ ((1 : ℝ) / 3)) :
    ∃ n : ℤ, M = n := by
  set a := (√5 + 2) ^ ((1 : ℝ) / 3) with ha
  set b := (√5 - 2) ^ ((1 : ℝ) / 3) with hb
  have ha₀ : 0 ≤ √5 + 2 := by positivity
  have hb₀ : 0 ≤ √5 - 2 := sub_nonneg.2 (Real.le_sqrt_of_sq_le (by norm_num))
  have hprod : a * b = 1 := by
    rw [ha, hb, ← Real.mul_rpow ha₀ hb₀]
    ring_nf
    norm_num
  replace ha : a ^ 3 = √5 + 2 := by
    norm_num [ha, ← Real.rpow_mul_natCast ha₀]
  replace hb : b ^ 3 = √5 - 2 := by
    norm_num [hb, ← Real.rpow_mul_natCast hb₀]
  have H : M ^ 3 = 4 - 3 * M := by
    calc M ^ 3
      _ = (a - b) ^ 3 := by rw [hM]
      _ = (a ^ 3 - b ^ 3) - 3 * (a * b) * (a - b) := by ring
      _ = (√5 + 2) - (√5 - 2) - 3 * 1 * M := by rw [ha, hb, hprod, hM]
      _ = 4 - 3 * M := by ring
  replace H : (M - 1) * (M ^ 2 + M + 4) = 0 := by linear_combination H
  simp [show M ^ 2 + M + 4 ≠ 0 by linarith only [sq_nonneg (2 * M + 1)], sub_eq_zero] at H
  exact ⟨1, by simp [H]⟩
