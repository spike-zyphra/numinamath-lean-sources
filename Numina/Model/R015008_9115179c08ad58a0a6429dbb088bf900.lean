import Mathlib

open Real

theorem algebra_13842 {x : ℝ} (hx : x > 0) (h : sqrt (7 - x) = 7 - x^2) :
    x = (-1 + sqrt 29) / 2 := by
  have h1 : 7 - x ≥ 0 := by 
    by_contra h2
    push_neg at h2
    have h3 : sqrt (7 - x) = 0 := by 
      rw [Real.sqrt_eq_zero']
      all_goals linarith 
    rw [h3] at h 
    nlinarith 
  have h3 : (7 - x) = (7 - x^2) ^ 2 := by 
    calc 
      7 - x = (sqrt (7 - x)) ^ 2 := by 
        rw [Real.sq_sqrt]
        linarith [h1]
      _ = (7 - x^2) ^ 2 := by 
        rw [h]
  have h4 : x^4 -14*x^2 +x +42 =0 := by
    nlinarith 
  have h5 : (x^2 +x -7) * (x+2) * (x-3) =0 := by
    nlinarith 
  cases' (mul_eq_zero.mp h5) with h6 h7
  · cases' (mul_eq_zero.mp h6) with h8 h9
    · -- Case 1: $x^2 +x -7=0$
      have h10 : x^2 +x -7 =0 := by
        nlinarith
      have h11 : (x - (-1 + Real.sqrt 29)/2) * (x - (-1 - Real.sqrt 29)/2) = 0 := by 
        nlinarith [ Real.sqrt_pos.mpr (show (0: ℝ) < 29 by norm_num), Real.sq_sqrt (show (29: ℝ) ≥0 by norm_num) ]
      cases' (mul_eq_zero.mp h11) with h12 h13
      · 
        nlinarith 
      · 
        nlinarith [ Real.sqrt_pos.mpr (show (0: ℝ) < 29 by norm_num), Real.sq_sqrt (show (29: ℝ) ≥0 by norm_num) ]
    · -- Case 2: $x+2=0$, contradicts $x>0$.
      nlinarith 
  · -- Case 3: $x-3=0$, i.e., $x=3$, which does not satisfy the original equation.
    have h14 : x =3 := by linarith 
    rw [h14] at h 
    -- This would imply $\sqrt{4}= -2$, which is false. Therefore, contradiction.
    -- First part of the equation: sqrt(7 -3) = sqrt(4) = 2.
    have h15 : sqrt (7 - (3: ℝ)) = (2: ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    -- Second part of the equation: 7 - 3^2 = -2.
    have h16 : (7 - (3: ℝ) ^2: ℝ) = (-2: ℝ) := by norm_num
    -- Comparing the two parts, $\sqrt{4} = -2 \implies 2 = -2$ which is False.
    nlinarith [ Real.sqrt_nonneg (7 - (3: ℝ)), h15, h16 ]