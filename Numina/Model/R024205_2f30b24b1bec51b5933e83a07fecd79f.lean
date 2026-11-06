import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_8606 :
  IsLeast {y : ℝ | ∃ x, y = sqrt ((x^4)/16 + (x^2)/2 + 1) + sqrt ((x^4)/16 - 4*x + 8)} 3 := by
  constructor 
  · -- Show 3 is in the set 
    use 2 
    have h1 : sqrt ((2^4 : ℝ)/16 + (2^2)/2 + 1) = 2 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    have h2 : sqrt ((2^4 : ℝ)/16 - 4*2 + 8) = 1 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    norm_num 
  · -- Show that 3 is the minimum element in the set 
    intro y hy 
    rcases hy with ⟨x, hx⟩ 
    have h1 : sqrt ((x^4 : ℝ)/16 + (x^2)/2 + 1) = (x^2 + 4)/4 := by 
      have h1 : ((x^4 : ℝ)/16 + (x^2)/2 + 1) = ((x^2 + 4)^2)/16 := by 
        ring_nf 
      have h2 : sqrt ((x^2 + 4)^2 / (16 : ℝ)) = ((x^2 + 4)/4) := by 
        have h3 : sqrt ((x^2 + 4)^2 / (16 : ℝ)) = sqrt ((x^2 + 4)^2) / sqrt (16 : ℝ) := by 
          field_simp [sqrt_div]
        have h4 : sqrt ((x^2 + 4)^2) = x^2 + 4 := by 
          rw [Real.sqrt_sq (show 0 ≤ x^2 + 4 by positivity)]
        have h5 : sqrt (16 : ℝ) = 4 := by 
          rw [Real.sqrt_eq_cases]
          all_goals norm_num 
        rw [h3, h4, h5] 
        <;> ring_nf  
      rw [h1] 
      rw [h2] 
    have h4 : sqrt ((x^4 : ℝ)/16 + (x^2)/2 + 1) + sqrt ((x^4 : ℝ)/16 - 4*x + 8) ≥ 3 := by 
      by_cases h4 : (2 - (x^2 : ℝ)/4) ≥ 0 
      · -- Case where $2 - \frac{x^2}{4} \geq 0$ 
        have h5 : sqrt ((x^4 : ℝ)/16 - 4*x + 8) ≥ (2 - (x^2 : ℝ)/4) := by
          have h8 : ( (x^4 : ℝ)/16 - 4*x + 8 ) ≥ 0 := by 
            nlinarith [sq_nonneg (x^2 - 8), sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x^2 - 4)]
          have h9 : ( (x^4 : ℝ)/16 - 4*x + 8 ) ≥ ( (2 - (x^2 : ℝ)/4 )^2 ) := by
            nlinarith [sq_nonneg (x - 2), sq_nonneg (x^2 - 4)]
          have h10 : sqrt ((x^4 : ℝ)/16 - 4*x + 8) ≥ (sqrt ((2 - (x^2 : ℝ)/4 )^2 )) := by 
            apply Real.sqrt_le_sqrt 
            nlinarith 
          have h11 : sqrt ((2 - (x^2 : ℝ)/4 )^2 ) = (2 - (x^2 : ℝ)/4 ) := by 
            rw [Real.sqrt_sq] 
            nlinarith 
          linarith [h10, h11]
        have h12 : sqrt ((x^4 : ℝ)/16 + (x^2)/2 + 1) + sqrt ((x^4 : ℝ)/16 - 4*x + 8) ≥ 3 := by
          nlinarith [Real.sqrt_nonneg ((x^4 : ℝ)/16 + (x^2)/2 + 1), Real.sqrt_nonneg ((x^4 : ℝ)/16 - 4*x + 8), sq_nonneg (x - 2), sq_nonneg (x^2 - 4)]
        linarith 
      · -- Case where $2 - \frac{x^2}{4} < 0$ 
        have h5 : sqrt ((x^4 : ℝ)/16 - 4*x + 8) ≥ (2 - (x^2 : ℝ)/4) := by 
          have h6 : (2 - (x^2 : ℝ)/4 : ℝ) < 0 := by linarith 
          have h7 : sqrt ((x^4 : ℝ)/16 - 4*x + 8) ≥ 0 := Real.sqrt_nonneg ((x^4 : ℝ)/16 - 4*x + 8)
          linarith 
        have h12 : sqrt ((x^4 : ℝ)/16 + (x^2)/2 + 1) + sqrt ((x^4 : ℝ)/16 - 4*x + 8) ≥ 3 := by 
          nlinarith [Real.sqrt_nonneg ((x^4 : ℝ)/16 + (x^2)/2 + 1), Real.sqrt_nonneg ((x^4 : ℝ)/16 - 4*x + 8), sq_nonneg (x - 2), sq_nonneg (x^2 - 4)]
        linarith 
    linarith [h1, h4]