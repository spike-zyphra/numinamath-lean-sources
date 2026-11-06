import Mathlib

theorem inequalities_277085 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 ≥ √(a * b) := by
  have h1 : (√a - √b) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h2 : (√a - √b) ^ 2 = a + b - 2 * √(a * b) := by
    have h3 : √(a * b) = √a * √b := by
      rw [Real.sqrt_mul (by linarith)]
    have h4 : (√a - √b) ^ 2 = (√a) ^ 2 + (√b) ^ 2 - 2 * (√a * √b) := by 
      ring_nf
    have h5 : (√a) ^ 2 = a := Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith)
    have h6 : (√b) ^ 2 = b := Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith)
    rw [h4, h5, h6]
    rw [h3]
    all_goals linarith
  have h7 : a + b - 2 * √(a * b) ≥ 0 := by 
    linarith [h1, h2]
  linarith