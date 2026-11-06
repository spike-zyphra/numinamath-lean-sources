import Mathlib
open Real

/-Compute:
$$
\left|\frac{2005^3}{2003 \times 2004} - \frac{2003^3}{2004 \times 2005}\right|
$$-/

theorem algebra_611193:  ⌊ ( 2005 ^ 3 : ℝ) / ( 2003 * 2004 ) - ( 2003 ^ 3 : ℝ ) / ( 2004 * 2005 ) ⌋ = 8  := by 
  let a : ℝ := ( 2005 ^ 3 : ℝ) / ( 2003 * 2004 ) - ( 2003 ^ 3 : ℝ ) / ( 2004 * 2005 )
  let x : ℝ := 2004

  have h1:  a = 8 + 16 * x / (x^3 - x) := by 
    simp[a,x]
    ring_nf

  have ineq1: a ≥ 8  := by -- show that a is greater than 8.
    rw [h1]
    norm_num

  have ineq2: a < 9 := by -- show that a is less than 9.
    rw [h1]
    norm_num

  apply Int.floor_eq_iff.mpr 
  constructor
  exact ineq1
  dsimp
  norm_cast at ineq2
  norm_num
  

    
    

   


