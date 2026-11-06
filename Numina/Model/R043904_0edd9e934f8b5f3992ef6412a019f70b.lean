import Mathlib

theorem algebra_262460 (f : ℝ → ℝ) (hf : ∀ x > 0, f x > 0)
    (h : ∀ x y, x > 0 → y > 0 → f (y * f x) * (x + y) = x ^ 2 * (f x + f y)) :
    ∀ x > 0, f x = 1 / x := by 
  intro x hx
  have h1 : f 1 > 0 := hf 1 (by norm_num)
  have h2 : f x > 0 := hf x hx
  have eq8 : f 1 = 1 := by
    have eq9 := h 1 1 (by norm_num) (by norm_num)
    have eq10 : f (1 * f 1) * (1 + 1) = 1 ^ 2 * (f 1 + f 1) := by
      simpa using eq9
    have eq11 : f (f 1) * 2 = 2 * f 1 := by
      have eq12 : f (1 * f 1) * 2 = 2 * f 1 := by
        nlinarith [eq10]
      have eq13 : f (1 * f 1) = f (f 1) := by
        simp
      nlinarith [eq12, eq13]
    have eq6 : f (f 1) = f 1 := by
      nlinarith [eq11, h1]
    -- Apply h with x=f 1 and y=1
    have eq13 := h (f 1) 1 (show f 1 > 0 by linarith [h1] ) (by norm_num)
    have eq14 : f (1 * f (f 1)) * (f 1 + 1) = (f 1) ^ 2 * (f (f 1) + f 1) := by
      simpa using eq13
    rw [show f (f 1) = f 1 by linarith [eq6] ] at eq14
    have h12 : f 1 > 0 := h1
    have eq15 : f 1 * (f 1 + 1) = 2 * f 1 ^ 3 := by
      nlinarith [eq14]
    have eq16 : 2 * (f 1) ^ 2 - f 1 - 1 = 0 := by
      nlinarith [eq15, sq_pos_of_pos h12]
    have h12 : (f 1 - 1) * (2 * f 1 + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h12) with h13 h14
    ·
      linarith
    ·
      nlinarith
  have eq14 : f x * x = 1 := by
    have eq91 := h 1 x (by norm_num) hx
    rw [eq8] at eq91 
    simp at eq91 
    nlinarith 
  have eq15 : f x = 1 / x := by
    field_simp [show x ≠ 0 by linarith] at *
    nlinarith 
  exact eq15