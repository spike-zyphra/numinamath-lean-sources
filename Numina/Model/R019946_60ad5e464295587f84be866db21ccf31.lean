import Mathlib

open BigOperators Real Set


theorem inequalities_600135 {f : ℝ → ℝ} (hf : ∀ x ∈ Ioo 0 1, f x = 1 / (1 + x ^ 2) ^ 2) :
    ∀ x ∈ Ioo 0 1, f x ≤ -4096 / 4913 * x + 5376 / 4913 := by
  intro x hx
  have hfx : f x = 1 / (1 + x ^ 2) ^ 2 := hf x hx
  rw [hfx]
  have h1 : 0 < x := hx.1
  have h2 : x < 1 := hx.2
  have hx2_pos : 0 < 1 + x ^ 2 := by
    nlinarith [sq_pos_of_pos (show 0 < x by linarith : (0 : ℝ) < x), sq_nonneg (x)]
  have h3 : 0 < (1 + x ^ 2) ^ 2 := by positivity

  have h4 : 1 / (1 + x ^ 2) ^ 2 ≤ -4096 / 4913 * x + 5376 / 4913 := by
    have h5 : 0 < (1 + x ^ 2 : ℝ) := by nlinarith
    have h6 : 0 < (1 + x ^ 2 : ℝ) ^ 2 := by positivity
    have h7 : 0 < (4913 : ℝ) := by norm_num
    have h8 : 0 < (1 + x ^ 2) ^ 2 * (4913 : ℝ) := by positivity
    have h9 : 1 / (1 + x ^ 2) ^ 2 ≤ -4096 / 4913 * x + 5376 / 4913 := by
      have h10 : 1 / (1 + x ^ 2) ^ 2 - (-4096 / 4913 * x + 5376 / 4913) ≤ 0 := by
        have h11 : 1 / (1 + x ^ 2) ^ 2 - (-4096 / 4913 * x + 5376 / 4913) = 
            (1 * (4913 : ℝ) - (-4096 * x + 5376) * ((1 + x ^ 2) ^ 2)) / ((1 + x ^ 2) ^ 2 * (4913 : ℝ)) := by 
          field_simp
          ring
        rw [h11]
        have h12 : 1 * (4913 : ℝ) - (-4096 * x + 5376) * ((1 + x ^ 2) ^ 2) ≤ 0 := by
          nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1 / 4), sq_nonneg (x - 1), sq_nonneg (x * (x - 1 / 4)), sq_nonneg ((x) ^ 2 - (1 / 4)), sq_nonneg ((x) ^ 2 - (1 / 4) * (x ^ 2)), sq_nonneg ((x) * (x - 1 / 4)), sq_nonneg ((x) * (x * (x - 1 / 4))), sq_nonneg (x * (x - 1)), sq_nonneg ((x) ^ 2 - (1 / 4) ^ 2), mul_pos (show 0 < x by linarith) (show 0 < 1 - x by linarith), sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x ^ 2)]
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Numerator ≤ 0
          nlinarith
        · -- Denominator ≥ 0
          positivity
      linarith
    linarith
  exact h4