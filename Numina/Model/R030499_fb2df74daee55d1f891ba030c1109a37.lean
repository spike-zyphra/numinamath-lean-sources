import Mathlib

theorem algebra_201286 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y + 6 * x * y) (h' : f (-1) * f 1 ≥ 9) :
    f (2 / 3) = 4 / 3 := by
  have f0 : f 0 = 0 := by
    specialize h 0 0
    norm_num at h ⊢
    linarith
  have hfx : ∀ x, f x + f (-x) = 6 * x ^ 2 := by
    intro x
    have h1 := h x (-x)
    simp [show x + -x = (0 : ℝ) by ring] at h1
    linarith
  have h1_p1 : f 1 + f (-1) = 6 := by
    specialize hfx 1
    norm_num at hfx ⊢
    linarith
  have hf1_eq_3 : f 1 = 3 := by
    nlinarith [sq_nonneg (f 1 - 3), sq_nonneg (f (-1) - 3), sq_nonneg (f 1 - f (-1))]
  have h2_3_1 : f (2 / 3) = 2 * f (1 / 3) + 2 / 3 := by
    specialize h (1 / 3) (1 / 3)
    rw [show (1 / 3 : ℝ) + (1 / 3 : ℝ) = (2 / 3 : ℝ) by norm_num] at h
    linarith
  have h1' : f 1 = f (2 / 3) + f (1 / 3) + 4 / 3 := by
    specialize h (2 / 3) (1 / 3)
    rw [show (2 / 3 : ℝ) + (1 / 3 : ℝ) = (1 : ℝ) by norm_num] at h
    linarith
  have hf13_eq_13 : f (1 / 3) = 1 / 3 := by
    have hfx13 : f (1 / 3) + f (- (1 / 3)) = 6 * (1 / 3) ^ 2 := by
      specialize hfx (1 / 3)
      simpa using hfx
    have h1_n3 : f (1 / 3) + f (- (1 / 3)) = 2 / 3 := by
      linarith
    have h2_3_n13 : f ( - (1 / 3) ) = 2 / 3 - f (1 / 3) := by 
      linarith
    rw [h2_3_n13] at hfx13
    nlinarith [sq_nonneg (f (1 / 3) - 1 / 3), sq_nonneg (f (1 / 3) - 1 / 3)]
  rw [hf13_eq_13] at h2_3_1 h1'
  nlinarith [hf1_eq_3]