import Mathlib

open Real Set

theorem algebra_9546 {x : ℝ} (hx : x ∈ Ico 0 (Real.pi)) (h : tan x = 2 / sqrt 7) :
    1 + sin (2 * x) = 1 + 4 * sqrt 7 / 11 := by
  rcases hx with ⟨hx0, hxpi⟩
  have h1 : cos x ≠ 0 := by
    by_contra h2
    have htan : tan x = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h2]
    rw [htan] at h
    field_simp at h
  have h2 : sin x / cos x = 2 / sqrt 7 := by 
    rw [Real.tan_eq_sin_div_cos] at h
    exact h
  have h3 : sin x = 2 / sqrt 7 * cos x := by
    have h4 : cos x ≠ 0 := h1
    field_simp at h2 ⊢
    linarith
  have h4 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [h3] at h4
  have h5 : cos x ^ 2 = 7 / 11 := by
    have h6 : (2 / sqrt 7 * cos x) ^ 2 + cos x ^ 2 = 1 := by
      linarith
    have h7 : (2 / sqrt 7 * cos x) ^ 2 = (4 / 7) * cos x ^ 2 := by
      calc
        (2 / sqrt 7 * cos x) ^ 2 = (4 / (sqrt 7 * sqrt 7)) * cos x ^ 2 := by ring_nf
        _ = (4 / (7 : ℝ)) * cos x ^ 2 := by 
          have h8 : sqrt 7 * sqrt 7 = (7 : ℝ) := by 
            calc
              sqrt 7 * sqrt 7 = (sqrt 7) ^ 2 := by ring
              _ = (7 : ℝ) := by rw [Real.sq_sqrt]; positivity
          rw [h8]
    rw [h7] at h6
    nlinarith [Real.sqrt_pos.mpr (show 0 < (7 : ℝ) by norm_num : (7 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (0 : ℝ) ≤ 7)]
  have h6 : sin (2 * x) = 2 * sin x * cos x := by 
    rw [show sin (2 * x) = 2 * sin x * cos x by rw [Real.sin_two_mul]]
  rw [h6]
  rw [h3]
  have h10 : 2 * (2 / sqrt 7 * cos x) * cos x = 4 * sqrt 7 / 11 := by
    have h11 : cos x ^ 2 = 7 / 11 := h5
    have h14 : 2 * (2 / sqrt 7 * cos x) * cos x = (4 / sqrt 7) * (cos x ^ 2) := by 
      field_simp
      all_goals nlinarith
    rw [h14, h11]
    have h17 : (4 / sqrt 7 : ℝ) * (7 / 11 : ℝ) = (4 * sqrt 7 / 11 : ℝ) := by
      have h19 : sqrt 7 ^ 2 = 7 := Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)
      field_simp [h19]
      <;> nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (0 : ℝ) ≤ 7)]
    linarith
  linarith