import Mathlib

theorem inequalities_598938 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    Real.sqrt a + Real.sqrt b + Real.sqrt c ≤ Real.sqrt 3 := by
  have h1 : (Real.sqrt a + Real.sqrt b + Real.sqrt c) ^ 2 ≤ 3 := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt b - Real.sqrt c), sq_nonneg (Real.sqrt c - Real.sqrt a),
      Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith), Real.sq_sqrt (show 0 ≤ c by linarith),
      h, Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c
      ]
  have h2 : Real.sqrt a + Real.sqrt b + Real.sqrt c ≤ Real.sqrt 3 := by
    have h3 : (Real.sqrt a + Real.sqrt b + Real.sqrt c) ^ 2 ≤ (3 : ℝ) := by
      linarith [h1]
    have h4 : 0 ≤ Real.sqrt 3 := by positivity
    have h8 : Real.sqrt ((Real.sqrt a + Real.sqrt b + Real.sqrt c) ^ 2) = Real.sqrt a + Real.sqrt b + Real.sqrt c := by
      have h7 : 0 ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
        positivity
      have h8 : (Real.sqrt a + Real.sqrt b + Real.sqrt c) ^ 2 ≥ 0 := by nlinarith
      rw [Real.sqrt_sq]
      all_goals nlinarith
    have h5 : Real.sqrt ((Real.sqrt a + Real.sqrt b + Real.sqrt c) ^ 2) ≤ Real.sqrt (3 : ℝ) := by
      apply Real.sqrt_le_sqrt
      nlinarith [h1]
    linarith [h8, h5]
  exact h2