import Mathlib

/- Given $a;b;c$ satisfying $a^{2}+b^{2}+c^{2}=2$ . Prove that:
a)  $\left | a+b+c-abc \right |\leqslant 2$ .
b)  $\left | a^{3}+b^{3}+c^{3}-3abc \right |\leqslant 2\sqrt{2}$ -/
theorem inequalities_56642
    (a b c : ℝ)
    (h : a^2 + b^2 + c^2 = 2): 
    (|a + b + c - a * b * c| ≤ 2 ∧ |a^3 + b^3 + c^3 - 3 * a * b * c| ≤ 2 * Real.sqrt 2) := by

  have h1 : -2 ≤ a + b + c - a * b * c := by 
    nlinarith [sq_nonneg (a + b + c - 2), sq_nonneg (a + b + c + 2), 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b + a * c + b * c - 1), 
          h, mul_self_nonneg (a + 1), mul_self_nonneg (b + 1), mul_self_nonneg (c + 1), 
          mul_self_nonneg (a - 1), mul_self_nonneg (b - 1), mul_self_nonneg (c - 1)]
  have h2 : a + b + c - a * b * c ≤ 2 := by 
    nlinarith [sq_nonneg (a + b + c - 2), sq_nonneg (a + b + c + 2), 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b + a * c + b * c - 1), 
          h, mul_self_nonneg (a + 1), mul_self_nonneg (b + 1), mul_self_nonneg (c + 1), 
          mul_self_nonneg (a - 1), mul_self_nonneg (b - 1), mul_self_nonneg (c - 1)]
  have h1' : |a + b + c - a * b * c| ≤ 2 := by 
    apply abs_le.mpr 
    constructor <;> linarith [h1, h2]
  have h3 : -2 * Real.sqrt 2 ≤ a^3 + b^3 + c^3 - 3 * a * b * c := by
    have h4 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg 2, sq_nonneg (a + b + c - Real.sqrt 2), sq_nonneg (a + b + c + Real.sqrt 2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, 
          sq_nonneg (a^2 + b^2 + c^2 - 2), sq_nonneg (a * b + a * c + b * c), 
          mul_self_nonneg (a - b), mul_self_nonneg (a - c), mul_self_nonneg (b - c)]
  have h4 : a^3 + b^3 + c^3 - 3 * a * b * c ≤ 2 * Real.sqrt 2 := by
    have h4 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg 2, sq_nonneg (a + b + c - Real.sqrt 2), sq_nonneg (a + b + c + Real.sqrt 2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, 
          sq_nonneg (a^2 + b^2 + c^2 - 2), sq_nonneg (a * b + a * c + b * c), 
          mul_self_nonneg (a - b), mul_self_nonneg (a - c), mul_self_nonneg (b - c)]
  have h2' : |a^3 + b^3 + c^3 - 3 * a * b * c| ≤ 2 * Real.sqrt 2 := by 
    apply abs_le.mpr 
    constructor 
    · linarith [h3]
    · linarith [h4]
  
  constructor 
  · -- Prove that |a + b + c - a * b * c| ≤ 2 
    exact h1'
  · -- Prove that |a^3 + b^3 + c^3 - 3 * a * b * c| ≤ 2 * Real.sqrt 2 
    exact h2'