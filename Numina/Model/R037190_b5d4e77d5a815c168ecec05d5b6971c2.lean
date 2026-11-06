import Mathlib

theorem algebra_12658 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (f : ℝ → ℝ)
    (hf : ∀ x, f x = 2 * (a - x) * (x + √(x ^ 2 + b ^ 2))) :
    IsGreatest (Set.range f) (a ^ 2 + b ^ 2) := by 
  constructor 
  · -- Show that $a^2 + b^2$ is in the range of f
    use (a^2 - b^2) / (2 * a)
    rw [hf]
    have hx1 : √ ( ((a^2 - b^2) / (2 * a)) ^ 2 + b ^ 2 ) = (a ^ 2 + b ^ 2) / (2 * a) := by 
      have h4 : ((a^2 - b^2) / (2 * a)) ^ 2 + b ^ 2 = ((a ^ 2 + b ^ 2) / (2 * a)) ^ 2 := by 
        field_simp
        nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2), mul_pos ha hb]
      rw [h4]
      have h5 : 0 ≤ (a ^ 2 + b ^ 2) / (2 * a) := by 
        apply div_nonneg 
        nlinarith [sq_nonneg a, sq_nonneg b, mul_pos ha hb]
        linarith [show 0 < (2 * a : ℝ) by linarith]
      rw [Real.sqrt_sq (by nlinarith [h5] ) ]
    have hx2 : 2 * (a - (a^2 - b^2) / (2 * a)) * (( (a^2 - b^2) / (2 * a) ) + ( (a ^ 2 + b ^ 2) / (2 * a) )) = a^2 + b^2 := by
      field_simp 
      <;> nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2) ]
    rw [hx1]
    linarith [hx2]
  · -- Show that $a^2 + b^2$ is greatest in range of $f$
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    have h3 : 2 * (a - x) * (x + √(x ^ 2 + b ^ 2)) ≤ a ^ 2 + b ^ 2 := by 
      have h4 : 0 ≤ a ^ 2 + b ^ 2 - 2 * (a - x) * (x + √(x ^ 2 + b ^ 2)) := by 
        have h6 : (√(x ^ 2 + b ^ 2)) ^ 2 = x^2 + b^2 := by
          rw [Real.sq_sqrt]
          positivity
        have h7 : a ^ 2 + b ^ 2 - 2 * (a - x) * (x + √(x ^ 2 + b ^ 2)) ≥ 0 := by
          have h8 : (a ^ 2 + b ^ 2 - 2 * (a - x) * (x + √(x ^ 2 + b ^ 2)) ) = 
            a ^ 2 - 2 * a * x + 2 * x ^ 2 + b ^ 2 - 2 * (a - x) * √(x ^ 2 + b ^ 2) := by 
            linarith 
          rw [h8] 
          have h9 : (√(x ^ 2 + b ^ 2)) ^ 2 = x ^ 2 + b ^ 2 := h6
          nlinarith [sq_nonneg ((a - x) - √(x ^ 2 + b ^ 2)), sq_nonneg (x - (a ^ 2 - b ^ 2) / (2 * a)), Real.sqrt_nonneg (x ^ 2 + b ^ 2), sq_nonneg (√(x ^ 2 + b^2) - (x + b/(2))), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + b ^ 2 by positivity), sq_nonneg (√(x ^ 2 + b^2) ^ 2 - x^2 - b^2), sq_nonneg ((a - x)), sq_nonneg ((x + √(x ^ 2 + b ^ 2))), mul_nonneg (Real.sqrt_nonneg (x ^ 2 + b ^ 2)) (Real.sqrt_nonneg (x ^ 2 + b ^ 2)), mul_pos ha hb, sq_nonneg (2 * x - a) ]
        linarith 
      linarith 
    linarith [h3, hx]