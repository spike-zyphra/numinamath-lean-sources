import Mathlib

theorem algebra_12517 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 - 3 * x) :
    {x | f (f x) = f x} = {0, 3, -1, 4}:= by 
  ext x 
  simp [hf]
  constructor 
  · -- First, if f(f(x)) = f(x), then x in {0,3,-1,4}
    intro h
    have h1 : x ^ 2 * (x - 3) * (x + 1) * (x - 4) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 3 * x - 2), sq_nonneg (x - 4), sq_nonneg (x + 1), sq_nonneg (x ^ 2 - 3 * x)]
    cases' (mul_eq_zero.mp h1) with h2 h2
    cases' (mul_eq_zero.mp h2) with h2 h2
    cases' (mul_eq_zero.mp h2) with h2 h2
    · -- When h1 = x ^ 2
      have h00 : x = 0 := by
        nlinarith
      simp [h00]
    · -- When h2 = x - 3
      have h00 : x = 3 := by
        nlinarith
      simp [h00]
    · -- When h2 = x + 1
      have h00 : x = -1 := by
        nlinarith
      simp [h00]
    · -- When h2 = x - 4
      have h00 : x = 4 := by
        nlinarith
      simp [h00]
  · -- Second, {0,3,-1,4} in {x | f(f(x)) = f(x)}
    rintro (rfl | rfl | rfl | rfl)
    · -- x = 0
      norm_num 
    · -- x = 3
      norm_num
    · -- x = -1
      norm_num 
    · -- x = 4
      norm_num