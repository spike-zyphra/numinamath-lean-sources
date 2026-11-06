import Mathlib

theorem inequalities_597879 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b + c - a) * (c + a - b) + (c + a - b) * (a + b - c) +
    (a + b - c) * (b + c - a) ≤
    Real.sqrt (a * b * c) * (Real.sqrt a + Real.sqrt b + Real.sqrt c) := by
  have ha1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have h1 : Real.sqrt (a * b * c) = Real.sqrt a * Real.sqrt b * Real.sqrt c := by
    have h5 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
      rw [Real.sqrt_mul (by linarith)]
      all_goals positivity
    have h6 : Real.sqrt (a * b * c) = Real.sqrt (a * b) * Real.sqrt c := by
      rw [Real.sqrt_mul (by positivity)]
      all_goals positivity
    rw [h6, h5]
    all_goals positivity
  have h2 : Real.sqrt (a * b * c) * (Real.sqrt a + Real.sqrt b + Real.sqrt c) =
      Real.sqrt a * Real.sqrt b * Real.sqrt c * (Real.sqrt a + Real.sqrt b + Real.sqrt c) := by 
    rw [h1]
    <;> ring_nf <;> simp [mul_add] <;> ring_nf <;> simp [mul_add] <;> ring_nf
  have h3 : Real.sqrt a ≥ 0 := Real.sqrt_nonneg a
  have h4 : Real.sqrt b ≥ 0 := Real.sqrt_nonneg b
  have h5 : Real.sqrt c ≥ 0 := Real.sqrt_nonneg c
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt b - Real.sqrt c), sq_nonneg (Real.sqrt a - Real.sqrt c), 
      sq_nonneg (Real.sqrt a + Real.sqrt b - Real.sqrt c), sq_nonneg (Real.sqrt b + Real.sqrt c - Real.sqrt a), sq_nonneg (Real.sqrt a + Real.sqrt c - Real.sqrt b), 
      Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ c by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ a * b * c by positivity), 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
      mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
      mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
      mul_pos (show 0 < a * b by positivity) (show 0 < a * c by positivity),
      mul_pos (show 0 < b * c by positivity) (show 0 < a * c by positivity)
      ]