import Mathlib

theorem algebra_9466 {a b c : ℝ} (ha : a > 0)
  (h : ∀ x, a * (2 + x) ^ 2 + b * (2 + x) + c = a * (2 - x) ^ 2 + b * (2 - x) + c)
  (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 2 + b * x + c) : f 0.5 > f Real.pi := by
  have h1 : b = -4 * a := by
    have eq1 := h 1
    have eq2 := h 0
    ring_nf at eq1 eq2
    linarith
  have h2 : f 0.5 = -1.75 * a + c := by
    rw [hf]
    simp [h1]
    <;> ring_nf
  have h3 : f Real.pi = a * (Real.pi ^ 2 - 4 * Real.pi) + c := by 
    rw [hf]
    simp [h1]
    <;> ring_nf
  rw [h2, h3]
  have h4 : 4 * Real.pi - Real.pi ^ 2 > (1.75 : ℝ) := by
    nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.sq_sqrt (show (0 : ℝ) ≤ (4 : ℝ) by norm_num), sq_nonneg (Real.pi - 2.5)]
  nlinarith [h4, mul_pos ha (show (0 : ℝ) < 1 by norm_num)]