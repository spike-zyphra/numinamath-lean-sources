import Mathlib


lemma lemma_1 (x : ℝ) (hx : x ≤ 3) : 1 / (x ^ 2 + 7) ≤ (5 - x) / 32 := by
  have h1 : x ^ 2 + 7 > 0 := by
    nlinarith [sq_nonneg x]
  have h2 : (5 - x) / 32 - 1 / (x ^ 2 + 7) ≥ 0 := by
    have pos1 : (x ^ 2 + 7) > 0 := h1
    have pos2 : (32 : ℝ) > 0 := by norm_num
    have h3 : (5 - x) * (x ^ 2 + 7) - 32 ≥ 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 3), sq_nonneg (x ^ 2 - 2 * x + 1), sq_nonneg (x - 1),
        sq_nonneg (x - 3), mul_nonneg (show 0 ≤ 3 - x by nlinarith) (show 0 ≤ (x - 1) ^ 2 by nlinarith)
      ]
    have h4 : (5 - x) / 32 - 1 / (x ^ 2 + 7) = ((5 - x) * (x ^ 2 + 7) - 32) / (32 * (x ^ 2 + 7)) := by
      field_simp
      <;> ring
    rw [h4]
    apply div_nonneg
    linarith
    positivity
  linarith


theorem inequalities_144845 (u v w : ℝ) (h : u + v + w = 3) :
    1 / (u ^ 2 + 7) + 1 / (v ^ 2 + 7) + 1 / (w ^ 2 + 7) ≤ 3 / 8 := by
  have h1 : w = 3 - u - v := by linarith
  rw [h1]
  have h2 : 1 / (u ^ 2 + 7) + 1 / (v ^ 2 + 7) + 1 / ((3 - u - v) ^ 2 + 7) ≤ 3 / 8 := by
    have h3 : 0 < (u ^ 2 + 7 : ℝ) := by nlinarith [sq_nonneg u]
    have h4 : 0 < (v ^ 2 + 7 : ℝ) := by nlinarith [sq_nonneg v]
    have h5 : 0 < ((3 - u - v : ℝ) ^ 2 + 7) := by nlinarith [sq_nonneg (3 - u - v : ℝ)]
    have h6 : (1 / (u ^ 2 + 7) + 1 / (v ^ 2 + 7) + 1 / ((3 - u - v) ^ 2 + 7) - 3 / 8) ≤ 0 := by
      have pos1 : 0 < (u ^ 2 + 7 : ℝ) := h3
      have pos2 : 0 < (v ^ 2 + 7 : ℝ) := h4
      have pos3 : 0 < ((3 - u - v : ℝ) ^ 2 + 7) := h5
      have h7 : (1 / (u ^ 2 + 7) + 1 / (v ^ 2 + 7) + 1 / ((3 - u - v : ℝ) ^ 2 + 7) - 3 / 8) =
          ( (8 * (v ^ 2 + 7) * ((3 - u - v) ^ 2 + 7) + 8 * (u ^ 2 + 7) * ((3 - u - v) ^ 2 + 7) + 8 * (u ^ 2 + 7) * (v ^ 2 + 7) - 3 * (u ^ 2 + 7) * (v ^ 2 + 7) * ((3 - u - v) ^ 2 + 7) ) / (8 * (u ^ 2 + 7) * (v ^ 2 + 7) * ((3 - u - v) ^ 2 + 7))) := by
        field_simp
        <;> ring
      rw [h7]
      apply div_nonpos_of_nonpos_of_nonneg
      nlinarith [sq_nonneg (u - 1 : ℝ), sq_nonneg (v - 1 : ℝ), sq_nonneg ((3 - u - v) - 1 : ℝ),
        sq_nonneg (u ^ 2 - 1 : ℝ), sq_nonneg (v ^ 2 - 1 : ℝ), sq_nonneg (((3 - u - v) ^ 2) - 1 : ℝ),
        sq_nonneg (u * v - 1 : ℝ), sq_nonneg (u * (3 - u - v) - 1 : ℝ), sq_nonneg (v * (3 - u - v) - 1 : ℝ),
        sq_nonneg (u - v : ℝ), sq_nonneg (u - (3 - u - v) : ℝ), sq_nonneg (v - (3 - u - v) : ℝ)
      ]
      positivity
    linarith
  linarith