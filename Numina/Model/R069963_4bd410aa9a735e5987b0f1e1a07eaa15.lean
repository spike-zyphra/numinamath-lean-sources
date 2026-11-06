import Mathlib

theorem algebra_244539 (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt x * (Real.sqrt x - 6) - 2 * (Real.sqrt x - 2) = -11 ↔ x = 9 ∨ x = 25 := by
  constructor
  · -- Assume $\sqrt{x}(\sqrt{x}-6)-2(\sqrt{x}-2) = -11$, prove $x = 9 ∨ x = 25$
    rintro h 
    have h1 : Real.sqrt x ^ 2 = x := by 
      exact Real.sq_sqrt hx 
    have h3 : Real.sqrt x ^ 2 - 8 * Real.sqrt x + 15 = 0 := by 
      nlinarith [h1] 
    have h4 : (Real.sqrt x - 3) * (Real.sqrt x - 5) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h4) with h5 h6 
    · -- Real.sqrt x - 3 = 0 
      have h7 : Real.sqrt x = 3 := by linarith 
      have h8 : x = 9 := by 
        calc 
          x = Real.sqrt x ^ 2 := by 
            rw [Real.sq_sqrt]
            all_goals linarith 
          _ = 3 ^ 2 := by 
            rw [h7]
          _ = (9 : ℝ) := by 
            norm_num 
      left 
      exact h8 
    · -- Real.sqrt x - 5 = 0 
      have h9 : Real.sqrt x = 5 := by linarith 
      have h10 : x = 25 := by 
        calc 
          x = Real.sqrt x ^ 2 := by 
            rw [Real.sq_sqrt]
            all_goals linarith 
          _ = 5 ^ 2 := by 
            rw [h9]
          _ = (25 : ℝ) := by 
            norm_num 
      right 
      exact h10 
  · -- Assume $x = 9 ∨ x = 25$, prove $\sqrt{x}(\sqrt{x}-6)-2(\sqrt{x}-2) = -11$
    rintro (h | h) 
    · -- Assume x = 9 
      rw [h] 
      have h2 : Real.sqrt (9 : ℝ) = 3 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h2]
      nlinarith 
    · -- Assume x = 25 
      rw [h] 
      have h3 : Real.sqrt (25 : ℝ) = 5 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h3]
      nlinarith