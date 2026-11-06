import Mathlib

theorem algebra_239962 {f : ℝ → ℝ} (h : ∀ x y, f (x * y) = f x + f y) (h' : f 2 = 1) :
    f (1 / 64) = -6 := by 
  have f4 : f 4 = 2 := by 
    have h1 := h 2 2
    norm_num at h1
    linarith [h']
  have f8 : f 8 = 3 := by 
    have h1 := h 2 4
    norm_num at h1
    linarith [h', f4]
  have f16 : f 16 = 4 := by 
    have h1 := h 2 8
    norm_num at h1
    linarith [h', f8]
  have f32 : f 32 = 5 := by 
    have h1 := h 2 16
    norm_num at h1
    linarith [h', f16]
  have f64 : f 64 = 6 := by 
    have h1 := h 2 32
    norm_num at h1
    linarith [h', f32]
  have f1 : f 1 = 0 := by 
    have h1 := h 1 1
    norm_num at h1
    linarith
  have h1 := h (1 / 64 : ℝ) 64
  have eq1 : (1 / 64 : ℝ) * (64 : ℝ) = 1 := by norm_num
  rw [eq1] at h1
  linarith [f1, f64, h1]