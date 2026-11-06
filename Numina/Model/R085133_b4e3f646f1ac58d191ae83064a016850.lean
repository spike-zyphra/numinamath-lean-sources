import Mathlib

theorem calculus_22162 {a c d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (h : !![a, 0; c, d] * !![a, c; 0, d] = !![4, -6; -6, 34]) :
    a = 2 ∧ c = -3 ∧ d = 5 := by
  have he11 : a^2 = 4 := by 
    have eq11 := congr_arg (λ m => m 0 0) h
    simp [Matrix.mul_apply] at eq11 
    nlinarith
  have he12 : a * c = -6 := by 
    have eq12 := congr_arg (λ m => m 0 1) h
    simp [Matrix.mul_apply] at eq12 
    linarith
  have he21 : a * c = -6 := by 
    have eq21 := congr_arg (λ m => m 1 0) h
    simp [Matrix.mul_apply] at eq21 
    linarith
  have he22 : c^2 + d^2 = 34 := by 
    have eq22 := congr_arg (λ m => m 1 1) h
    simp [Matrix.mul_apply] at eq22 
    nlinarith
  have ha2 : a = 2 := by
    nlinarith
  have hc3 : c = -3 := by
    rw [ha2] at he12
    nlinarith
  have hd5 : d = 5 := by
    rw [hc3] at he22
    nlinarith [sq_nonneg (d - 5)]
  exact ⟨ha2, hc3, hd5⟩