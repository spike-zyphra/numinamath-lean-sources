import Mathlib
theorem algebra_70646 (a b c : ℝ) (h : a * b * c = 1) : 2 * a - 1 / b ≤ 1 ∨ 2 * b - 1 / c ≤ 1 ∨ 2 * c - 1 / a ≤ 1:= by 
  by_contra h1
  push_neg at h1 
  rcases h1 with ⟨h11, h12, h13⟩ 
  have h1' : a ≠ 0 := by 
    by_contra h1'
    rw [h1'] at h 
    nlinarith 
  have h2' : b ≠ 0 := by 
    by_contra h2'
    rw [h2'] at h 
    nlinarith 
  have h4' : c ≠ 0 := by 
    by_contra h4'
    rw [h4'] at h 
    nlinarith 
  have h5 : (1 / b) = a * c := by 
    have h51 : b ≠ 0 := h2' 
    field_simp [h51]
    nlinarith 
  have h6 : (1 / c) = a * b := by 
    have h51 : c ≠ 0 := h4' 
    field_simp [h51]
    nlinarith 
  have h7 : (1 / a) = b * c := by 
    have h51 : a ≠ 0 := h1' 
    field_simp [h51]
    nlinarith 
  rw [h5] at h11 
  rw [h6] at h12 
  rw [h7] at h13 
  have eq1 : 2 * a - a * c > 1 := by linarith 
  have eq2 : 2 * b - a * b > 1 := by linarith 
  have eq3 : 2 * c - b * c > 1 := by linarith 
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), h, mul_pos (show 0 < 2 * a - a * c by nlinarith) (show 0 < 2 * b - a * b by nlinarith), mul_pos (show 0 < 2 * b - a * b by nlinarith) (show 0 < 2 * c - b * c by nlinarith), mul_pos (show 0 < 2 * c - b * c by nlinarith) (show 0 < 2 * a - a * c by nlinarith)]