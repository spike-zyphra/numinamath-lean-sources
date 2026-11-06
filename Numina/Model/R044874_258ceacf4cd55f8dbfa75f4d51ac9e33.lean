import Mathlib

open Real

theorem algebra_10340 {f : ℝ → ℝ} (hf : ∀ x, f x = cos x + logb 2 x) (a : ℝ)
    (ha : 0 < a) (h : f a = f (2 * a)) :
    f (2 * a) - f (4 * a) = -3 ∨ f (2 * a) - f (4 * a) = -1 := by
  have h1 : f a = cos a + logb 2 a := hf a
  have h2 : f (2 * a) = cos (2 * a) + logb 2 (2 * a) := hf (2 * a)
  rw [h1] at h
  rw [h2] at h
  have h3 : logb 2 (2 * a) = 1 + logb 2 a := by
    have h4 : logb 2 (2 * a) = logb 2 2 + logb 2 a := by
      rw [logb_mul (by linarith) (by linarith)]
    have h5 : logb 2 (2 : ℝ) = 1 := by
      norm_num [logb_eq_iff_rpow_eq]
    rw [h4, h5]
  rw [h3] at h
  have h4 : cos a - cos (2 * a) = 1 := by
    have h5 : cos a = cos (2 * a) + 1 := by
      nlinarith
    linarith
  have h5 : cos (2 * a) = 2 * (cos a)^2 - 1 := by
    rw [cos_two_mul]
  have h6 : cos a * (1 - 2 * cos a) = 0 := by
    have h7 : cos a - cos (2 * a) = 1 := h4
    rw [h5] at h7
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- case $\cos a = 0$
    have hc0 : cos a = 0 := h7
    have hc2a : cos (2 * a) = -1 := by
      rw [h5]
      rw [hc0]
      norm_num
    have hc4a : cos (4 * a) = 1 := by
      have h6 : cos (4 * a) = 2 * (cos (2 * a)) ^ 2 - 1 := by
        have h5' : 4 * a = 2 * (2 * a) := by ring
        rw [h5']
        rw [cos_two_mul]
      rw [h6, hc2a]
      norm_num
    have h11 : f (2 * a) - f (4 * a) = -3 := by
      have h7 : f (2 * a) = cos (2 * a) + logb 2 (2 * a) := hf (2 * a)
      have h8 : f (4 * a) = cos (4 * a) + logb 2 (4 * a) := hf (4 * a)
      rw [h7, h8]
      have h9 : logb 2 (4 * a) = 2 + logb 2 a := by
        have h10 : logb 2 (4 * a) = logb 2 4 + logb 2 a := by
          rw [logb_mul (by linarith) (by linarith)]
        have h11 : logb 2 (4 : ℝ) = 2 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        rw [h10, h11]
      have h12 : logb 2 (2 * a) = 1 + logb 2 a := h3
      rw [h12, h9, hc2a, hc4a]
      ring
    left
    linarith
  · -- case $1 - 2\cos a = 0$, i.e., $\cos a = \frac{1}{2}$
    have hc12 : cos a = 1 / 2  := by
      linarith
    have hc2a : cos (2 * a) = -1 / 2 := by
      rw [h5]
      rw [hc12]
      norm_num
    have hc4a : cos (4 * a) = -1 / 2 := by
      have h9 : cos (4 * a) = 2 * (cos (2 * a)) ^ 2 - 1 := by
        have h10 : 4 * a = 2 * (2 * a)  :=  by ring
        rw [h10]
        rw [cos_two_mul]
      rw [h9, hc2a]
      norm_num
    have h11 : f (2 * a) - f (4 * a) = -1 := by
      have h7 : f (2 * a) = cos (2 * a) + logb 2 (2 * a) := hf (2 * a)
      have h8  : f (4 * a) = cos (4 * a) + logb 2 (4 * a) := hf (4 * a)
      rw [h7, h8]
      have h12  : logb 2 (4 * a) = 2 + logb 2 a :=  by
        have h10 : logb 2 (4 * a) =  logb 2 4 +  logb 2 a := by
          rw [logb_mul (by  linarith) (by  linarith)]
        have h11 : logb 2 (4 : ℝ) = 2 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        rw [h10, h11]
      have h13 : logb 2 (2 * a) =  1 +  logb 2 a := h3
      rw [h13, h12, hc2a, hc4a]
      ring
    right
    linarith