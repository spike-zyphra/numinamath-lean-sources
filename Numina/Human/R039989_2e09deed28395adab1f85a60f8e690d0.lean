import Mathlib

/- Let $a,$ $b,$ $c$ be positive real numbers.  Find the minimum value of
\[\left( 2a + \frac{1}{3b} \right)^2 + \left( 2b + \frac{1}{3c} \right)^2 + \left( 2c + \frac{1}{3a} \right)^2.\] -/
theorem algebra_18880 :
    IsLeast {x | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ x = (2 * a + 1 / (3 * b)) ^ 2 + (2 * b + 1 / (3 * c)) ^ 2 + (2 * c + 1 / (3 * a)) ^ 2} 8 := by
  -- Simplify the goal into two parts.
  simp [IsLeast, lowerBounds, -one_div]
  refine ⟨?_, ?_⟩
  . -- Show that there exists (a, b, c) such that the minimum is attained.
    use 1 / Real.sqrt 6
    refine ⟨by positivity, ?_⟩
    use 1 / Real.sqrt 6
    refine ⟨by positivity, ?_⟩
    use 1 / Real.sqrt 6
    refine ⟨by positivity, ?_⟩
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  . -- Show that is the lower bound of all possible values.
    intro x a apos b bpos c cpos hx
    rw [hx]
    clear x hx
    ring_nf
    rw [<-one_div, <-one_div, <-one_div]
    have h₁ : (((4 * a ^ 2) * (4 * b ^ 2) * (4 * c ^ 2)) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) * (((1 / (9 * a ^ 2)) * (1 / (9 * b ^ 2)) * (1 / (9 * c ^ 2))) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) * ((4 * a ^ 2) * (4 * b ^ 2) * (4 * c ^ 2)) ^ (1 / 3 : ℝ) + (1 / 2 : ℝ) * ((1 / (9 * a ^ 2)) * (1 / (9 * b ^ 2)) * (1 / (9 * c ^ 2))) ^ (1 / 3 : ℝ) := by
      apply Real.geom_mean_le_arith_mean2_weighted
      all_goals
        try positivity
        try norm_num
    have h₂ : (1 / 2 : ℝ) * ((4 * a ^ 2) * (4 * b ^ 2) * (4 * c ^ 2)) ^ (1 / 3 : ℝ) + (1 / 2 : ℝ) * ((1 / (9 * a ^ 2)) * (1 / (9 * b ^ 2)) * (1 / (9 * c ^ 2))) ^ (1 / 3 : ℝ) ≤ (1 / 2 : ℝ) * ((1 / 3 : ℝ) * (4 * a ^ 2 + 4 * b ^ 2 + 4 * c ^ 2)) + (1 / 2 : ℝ) * ((1 / 3 : ℝ) * (1 / (9 * a ^ 2) + 1 / (9 * b ^ 2) + (1 / (9 * c ^ 2)))) := by
      apply add_le_add
      . simp [-one_div]
        rw [Real.mul_rpow, Real.mul_rpow, mul_add, mul_add]
        apply Real.geom_mean_le_arith_mean3_weighted
        all_goals
          try positivity
          try norm_num
      . simp [-one_div]
        rw [Real.mul_rpow, Real.mul_rpow, mul_add, mul_add]
        apply Real.geom_mean_le_arith_mean3_weighted
        all_goals
          try positivity
          try norm_num
    have h₃ : (4 * a / (3 * b)) ^ (1 / 3 : ℝ) * (4 * b / (3 * c)) ^ (1 / 3 : ℝ) * (4 * c / (3 * a)) ^ (1 / 3 : ℝ) ≤ (1 / 3 : ℝ) * (4 * a / (3 * b)) + (1 / 3 : ℝ) * (4 * b / (3 * c)) + (1 / 3 : ℝ) * (4 * c / (3 * a)) := by
      apply Real.geom_mean_le_arith_mean3_weighted
      all_goals
        try positivity
        try norm_num
    -- Simplify the goal using h₁, h₂, h₃.
    rw [show a * (1 / b) * (4 / 3 : ℝ) + a ^ 2 * 4 + b * (1 / c) * (4 / 3 : ℝ) + b ^ 2 * 4 + (1 / b) ^ 2 * (1 / 9 : ℝ) + c * (1 / a) * (4 / 3 : ℝ) + c ^ 2 * 4 + (1 / c) ^ 2 * (1 / 9 : ℝ) + (1 / a) ^ 2 * (1 / 9 : ℝ) = 6 * ((1 / 2 : ℝ) * ((1 / 3 : ℝ) * (4 * a ^ 2 + 4 * b ^ 2 + 4 * c ^ 2)) + (1 / 2 : ℝ) * ((1 / 3 : ℝ) * (1 / (9 * a ^ 2) + 1 / (9 * b ^ 2) + 1 / (9 * c ^ 2)))) + 3 * ((1 / 3 : ℝ) * (4 * a / (3 * b)) + (1 / 3 : ℝ) * (4 * b / (3 * c)) + (1 / 3 : ℝ) * (4 * c / (3 * a))) by field_simp; ring_nf]
    calc
      8 = 6 * (4 / 6 : ℝ) + 3 * (4 / 3 : ℝ) := by norm_num
      _ = 6 * (((4 * a ^ 2 * (4 * b ^ 2) * (4 * c ^ 2)) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) * ((1 / (9 * a ^ 2) * (1 / (9 * b ^ 2)) * (1 / (9 * c ^ 2))) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ)) + 3 * ((4 * a / (3 * b)) ^ (1 / 3 : ℝ) * (4 * b / (3 * c)) ^ (1 / 3 : ℝ) * (4 * c / (3 * a)) ^ (1 / 3 : ℝ)) := by
        rw [<-Real.mul_rpow, <-Real.mul_rpow, <-Real.rpow_mul, <-Real.mul_rpow, <-Real.mul_rpow]
        congrm 6 * ?_ + 3 * ?_
        . rw [show (4 / 6 : ℝ) = ((4 / 6 : ℝ) ^ (6 : ℝ)) ^ (1 / 3 * (1 / 2) : ℝ) by rw [<-Real.rpow_mul, show 6 * (1 / 3 * (1 / 2) : ℝ) = 1 by norm_num]; simp; norm_num]
          congrm ?_ ^ (1 / 3 * (1 / 2))
          field_simp
          ring_nf
        . rw [show (4 / 3 : ℝ) = ((4 / 3 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) by rw [<-Real.rpow_mul, show 3 * (1 / 3 : ℝ) = 1 by norm_num]; simp; norm_num]
          congrm ?_ ^ (1 / 3)
          field_simp
          ring_nf
        all_goals
          positivity
      _ ≤ 6 * ((1 / 2 : ℝ) * ((1 / 3 : ℝ) * (4 * a ^ 2 + 4 * b ^ 2 + 4 * c ^ 2)) + (1 / 2 : ℝ) * ((1 / 3 : ℝ) * (1 / (9 * a ^ 2) + 1 / (9 * b ^ 2) + 1 / (9 * c ^ 2)))) + 3 * ((1 / 3 : ℝ) * (4 * a / (3 * b)) + (1 / 3 : ℝ) * (4 * b / (3 * c)) + (1 / 3 : ℝ) * (4 * c / (3 * a))) := by
        apply add_le_add
        . simp [-one_div]
          exact h₁.trans h₂
        . simp [-one_div]
          exact h₃
