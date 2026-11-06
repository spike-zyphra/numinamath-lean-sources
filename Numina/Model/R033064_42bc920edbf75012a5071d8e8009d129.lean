import Mathlib

theorem algebra_15618  : {x : ℝ | x^4 + (2 - x)^4 = 34 } = {1 + Real.sqrt 2, 1 - Real.sqrt 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First direction: if x^4 + (2 - x)^4 = 34 then x = 1 ± Real.sqrt 2
    intro h
    have eq1 : x^4 + (2 - x) ^ 4 = 34 := by linarith
    have h2 : (x - (1 + Real.sqrt 2)) * (x - (1 - Real.sqrt 2)) = 0 := by
      nlinarith [sq_nonneg ((x - 1) ^ 2 - 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg ( (Real.sqrt 2: ℝ) ^ 2 - 2), sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x - 0), Real.sqrt_nonneg 2
      ]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- First case $h3: x - (1 + \sqrt{2}) = 0$. 
      left 
      linarith 
    · -- Second case $h4: x - (1 - \sqrt{2}) = 0$. 
      right 
      nlinarith 
  · -- Second direction: if x = 1 ± Real.sqrt 2 then x^4 + (2 - x)^4 = 34 
    rintro (h | h)
    · -- x = 1 + Real.sqrt 2 
      rw [h] 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg ( (1 + Real.sqrt 2: ℝ) ^ 2 - 2 ^ 2), Real.sqrt_nonneg 2 
      ]
    · -- x = 1 - Real.sqrt 2 
      rw [h] 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg ( (1 - Real.sqrt 2: ℝ) ^ 2 - 2 ^ 2), Real.sqrt_nonneg 2 
      ]