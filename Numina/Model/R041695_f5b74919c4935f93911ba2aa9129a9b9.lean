import Mathlib

theorem algebra_124310 (p : ℝ → ℝ) (hp : p = fun x => x^3 - 3 * x^2 + 5 * x)
    (h k : ℝ) (hroot : p h = 1) (kroot : p k = 5) : h + k = 2 := by

  have eq1 : h ^ 3 - 3 * h ^ 2 + 5 * h = 1 := by
    rw [hp] at hroot
    simp at hroot ⊢
    linarith

  have eq2 : k ^ 3 - 3 * k ^ 2 + 5 * k = 5 := by
    rw [hp] at kroot
    simp at kroot ⊢
    linarith
  
  -- Subtract 1 from both sides to get the polynomial form
  have eqh : h^3 - 3 * h^2 + 5 * h - 1 = 0 := by linarith

  -- Subtract 5 from both sides to get the polynomial form
  have eqk : k^3 - 3 * k^2 + 5 * k - 5 = 0 := by linarith

  nlinarith [sq_nonneg (h - k), sq_nonneg (h - 1), sq_nonneg (k - 1), sq_nonneg (h + k - 2), sq_nonneg (h - 2 + k), sq_nonneg (k - (2 - h)), sq_nonneg (h - (2 - k)), sq_nonneg (h ^ 2 + k ^ 2 - 4)]