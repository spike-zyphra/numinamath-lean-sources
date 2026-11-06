import Mathlib

/- Simplify the following expression to a simplified fraction: $$\sqrt{\dfrac{\dfrac{5}{\sqrt{80}}+\dfrac{\sqrt{845}}{9}+\sqrt{45}}{\sqrt5}}.$$ -/
theorem algebra_21644 : Real.sqrt (((5 / Real.sqrt 80) + (Real.sqrt 845 / 9) + Real.sqrt 45) / Real.sqrt 5) = 13 / 6 := by
  -- Simplify each term inside the square root
  -- $5 / \sqrt{80} / \sqrt{5} = 1 / 4$
  have h1 : 5 / Real.sqrt 80 / Real.sqrt 5 = 1 / 4 := by
    calc
      5 / Real.sqrt 80 / Real.sqrt 5 = 5 / (Real.sqrt 80 * Real.sqrt 5) := by field_simp
      _ = 5 / Real.sqrt (80 * 5) := by field_simp
      _ = 5 / Real.sqrt 400 := by norm_num
      _ = 5 / 20 := by
        have mid : √400 = 20 := by
          refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
          exact Nat.ofNat_pos'
          norm_num
        rw [mid]
      _ = 1 / 4 := by norm_num
  -- $\sqrt{845} / (9 * \sqrt{5}) = 13 / 9$
  have h2 : Real.sqrt 845 / 9 / Real.sqrt 5 = 13 / 9 := by
    calc
      _ = Real.sqrt 845 / (9 * Real.sqrt 5) := by field_simp
      _ = Real.sqrt 845 / Real.sqrt (9^2 * 5) := by field_simp
      _ = Real.sqrt 845 / Real.sqrt 405 := by norm_num
      _ = Real.sqrt (845 / 405) := by 
        rw [Real.sqrt_div]
        exact Nat.ofNat_nonneg' 845
      _ = Real.sqrt (169 / 81) := by norm_num
      _ = Real.sqrt 169 / Real.sqrt 81 := by 
        rw [Real.sqrt_div]
        exact Nat.ofNat_nonneg' 169
      _ = 13 / 9 := by 
        have mid : √169 = 13 := by
          refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
          exact Nat.ofNat_pos'
          norm_num
        have mid2 : √81 = 9 := by
          refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
          exact Nat.ofNat_pos'
          norm_num
        rw [mid, mid2]
  -- $\sqrt{45} / \sqrt{5} = 3$
  have h3 : Real.sqrt 45 / Real.sqrt 5 = 3 := by
    calc
      Real.sqrt 45 / Real.sqrt 5
          = Real.sqrt (45 / 5) := by 
            rw [Real.sqrt_div]
            exact Nat.ofNat_nonneg' 45
      _ = Real.sqrt 9 := by norm_num
      _ = 3 := by 
        refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
        exact Nat.ofNat_pos'
        norm_num

  -- Combine the simplified terms
  calc
    Real.sqrt (((5 / Real.sqrt 80) + (Real.sqrt 845 / 9) + Real.sqrt 45) / Real.sqrt 5)
        = Real.sqrt ((1 / 4 + 13 / 9 + 3)) := by 
          rw [add_div, add_div, h1, h2, h3]
    _ = Real.sqrt (169 / 36) := by norm_num
    _ = Real.sqrt (169) / Real.sqrt (36) := by 
      rw [Real.sqrt_div]
      exact Nat.ofNat_nonneg' 169
    _ = 13 / 6 := by
      have mid : √169 = 13 := by
        refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
        exact Nat.ofNat_pos'
        norm_num
      have mid2 : √36 = 6 := by
        refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
        exact Nat.ofNat_pos'
        norm_num
      rw [mid, mid2]

