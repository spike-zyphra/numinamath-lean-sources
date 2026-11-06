import Mathlib

/- 2. Given $x=\frac{1}{\sqrt{3}-\sqrt{2}}$. Then $x^{6}-2 \sqrt{2} x^{5}-x^{4}$ $+x^{3}-2 \sqrt{3} x^{2}+2 x-\sqrt{2}$ is $\qquad$.-/
theorem algebra_322405 (x : ℝ) (hx : x = 1 / (Real.sqrt 3 - Real.sqrt 2)) :
    x ^ 6 - 2 * Real.sqrt 2 * x ^ 5 - x ^ 4 + x ^ 3 - 2 * Real.sqrt 3 * x ^ 2 + 2 * x - Real.sqrt 2 = Real.sqrt 3 := by
  -- It suffices to tell the fact that √2³ = 2√2, √2⁴ = 4, √2⁵ = 4√2, √2⁶ = 8, √2⁷ = 8√2 and also the powers of √3 to field_simp.
  have h₀ : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num)]
  have h₁ : Real.sqrt 2 ^ 4 = 4 := by
    rw [pow_succ, h₀, mul_assoc, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have h₂ : Real.sqrt 2 ^ 5 = 4 * Real.sqrt 2 := by
    rw [pow_succ, h₁]
  have h₃ : Real.sqrt 2 ^ 6 = 8 := by
    rw [pow_succ, h₂, mul_assoc, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have h₄ : Real.sqrt 2 ^ 7 = 8 * Real.sqrt 2 := by
    rw [pow_succ, h₃]
  have g₀ : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num)]
  have g₁ : Real.sqrt 3 ^ 4 = 9 := by
    rw [pow_succ, g₀, mul_assoc, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have g₂ : Real.sqrt 3 ^ 5 = 9 * Real.sqrt 3 := by
    rw [pow_succ, g₁]
  have g₃ : Real.sqrt 3 ^ 6 = 27 := by
    rw [pow_succ, g₂, mul_assoc, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have g₄ : Real.sqrt 3 ^ 7 = 27 * Real.sqrt 3 := by
    rw [pow_succ, g₃]
  -- Also we have (√3 - √2)ⁿ ≠ 0 for various powers.
  have k₀ : Real.sqrt 3 - Real.sqrt 2 > 0 := by
    apply sub_pos_of_lt
    apply Real.sqrt_lt_sqrt
    <;> norm_num
  -- Let y = √3 - √2 = 1 / x and substitute x = 1 / y.
  let y := 1 / x
  have hy : y = Real.sqrt 3 - Real.sqrt 2 := by
    simp [y, hx]
  rw [<-hy] at k₀
  rw [show x = 1 / y by simp [y]]
  clear_value y
  -- Multiply both sides by y⁶ to clear denominators.
  rw [<-mul_left_inj' (show y ^ 6 ≠ 0 by positivity)]
  ring_nf
  -- Simplify the expression.
  repeat rw [<-zpow_natCast]
  repeat rw [inv_zpow']
  rw [<-zpow_neg_one]
  repeat rw [<-zpow_add₀ (by positivity)]
  norm_num [hy]
  -- Change the index of power back to natural number type in order to use ring_nf.
  norm_cast
  ring_nf
  field_simp [h₀, h₁, h₂, h₃, h₄, g₀, g₁, g₂, g₃, g₄]
  ring