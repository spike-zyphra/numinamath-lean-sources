import Mathlib

theorem algebra_4301 {a b : ℝ} (h₀ : a + b = 3) (h₁ : a ^ 2 * b + 3 * a * b + 8 = 0) :
    a * b * (a ^ 2 + 3 * b) + a ^ 2 * b * (3 + b) + 2 * (a + b) = -18 := by
  have h2 : b = 3 - a := by linarith
  rw [h2] at h₁
  have h3 : a ^ 3 - 9 * a - 8 = 0 := by 
    nlinarith
  have h4 : (a + 1) * (a ^ 2 - a - 8) = 0 := by 
    ring_nf at h3 ⊢
    linarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case $a + 1 = 0$, so $a = -1$ and $b = 4$.
    have ha : a = -1 := by linarith
    have hb : b = 4 := by 
      linarith [ha, h2]
    rw [ha, hb]
    norm_num
  · -- Case $a^2 - a - 8 = 0$:
    have h7 : a ^ 2 = a + 8 := by linarith
    rw [show b = 3 - a by linarith]
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 4), sq_nonneg (a - (-1)), sq_nonneg (a * (3 - a)), sq_nonneg (a ^ 2 - a - 8)]