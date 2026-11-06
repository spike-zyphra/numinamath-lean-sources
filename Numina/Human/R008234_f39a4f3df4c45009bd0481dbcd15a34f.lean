import Mathlib

/- 2. Let $a$ be any real number, prove: $a^{6}-a^{5}+a^{4}+a^{2}-a+1>0$.

 -/
theorem inequalities_127839 (a : ℝ) : a^6 - a^5 + a^4 + a^2 - a + 1 > 0 := by 
  have h1 : a^6 - a^5 + a^4 + a^2 - a + 1 = ((a - 1/2)^2 + 3 / 4) * (a^4 + 1) := by ring
  have h2 : ((a - 1/2)^2 + 3 / 4) > 0 := by 
    apply add_pos_of_nonneg_of_pos
    · apply pow_two_nonneg  
      -- (a - 1/2)² ≥ 0
    · norm_num             
      -- 3/4 > 0
  have h3_0 : a^4 + 1 = (a^2)^2 + 1 := by ring
  have h3 : (a^4 + 1) > 0 := by
    rw [h3_0]
    apply add_pos_of_nonneg_of_pos
    · apply pow_two_nonneg  
      -- a⁴ = (a²)² ≥ 0
    · norm_num              
      -- 1 > 0
  have h4 : ((a - 1/2)^2 + 3 / 4) * (a^4 + 1) > 0 := by apply mul_pos h2 h3
  exact lt_of_lt_of_eq h4 (id (Eq.symm h1))