import Mathlib

theorem algebra_217203 :
    {x : ℝ | x^2 + x + 7 ≥ 0 ∧ x^2 + x + Real.sqrt (x^2 + x + 7) = 5} = 
    {-2, 1} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
    and_imp]
  constructor
  · -- Assume (x ^ 2 + x + 7 ≥ 0 ∧ x ^ 2 + x + Real.sqrt (x ^ 2 + x + 7) = 5), prove (-2 = x ∨ 1 = x)
    intro h
    rcases h with ⟨h1, h2⟩
    have h4 : Real.sqrt (x ^ 2 + x + 7) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h5 : x ^ 2 + x + Real.sqrt (x ^ 2 + x + 7) = 5 := by
      linarith
    have h6 : (Real.sqrt (x ^ 2 + x + 7)) ^ 2 = x ^ 2 + x + 7 := by 
      rw [Real.sq_sqrt]
      linarith
    have h7 : (Real.sqrt (x ^ 2 + x + 7)) ^ 2 + Real.sqrt (x ^ 2 + x + 7) - 12 = 0 := by
      nlinarith [h5, h6]
    have h8 : (Real.sqrt (x ^ 2 + x + 7) - 3) * (Real.sqrt (x ^ 2 + x + 7) + 4) = 0 := by
      nlinarith [h7]
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case Y - 3 = 0, so y = 3.
      have h11 : Real.sqrt (x ^ 2 + x + 7) = 3 := by
        nlinarith 
      have h12 : x ^ 2 + x + 7 = 9 := by
        have h13 : Real.sqrt (x ^ 2 + x + 7) = 3 := h11
        have h14 : (Real.sqrt (x ^ 2 + x + 7)) ^ 2 = 9 := by 
          rw [h13]
          norm_num
        have h15 : (Real.sqrt (x ^ 2 + x + 7)) ^ 2 = x ^ 2 + x + 7 := by
          rw [Real.sq_sqrt]
          linarith
        linarith [h14, h15]
      have h13 : x ^ 2 + x - 2 = 0 := by
        nlinarith [h12]
      have h14 : (x + 2) * (x - 1) = 0 := by
        nlinarith [h13]
      cases' (mul_eq_zero.mp h14) with h15 h16
      · -- x + 2 =0, then x=-2
        left
        linarith
      · -- x -1 =0, then x=1
        right
        linarith
    · -- Case y + 4 =0, so y = -4, which contradicts with y >=0
      have h11 : Real.sqrt (x ^ 2 + x + 7) = -4 := by
        nlinarith 
      nlinarith [Real.sqrt_nonneg (x ^ 2 + x + 7), Real.sq_sqrt (show (x^2 + x + 7 : ℝ) ≥ 0 by linarith [h1]), h11]
  · -- Assume (-2 = x ∨ 1 = x), prove (x ^ 2 + x + 7 ≥ 0 ∧ x ^ 2 + x + Real.sqrt (x ^ 2 + x + 7) = 5)
    intro h
    rcases h with (rfl | rfl)
    · -- x = -2
      constructor
      · norm_num
      · -- Show $x^2 +x + \sqrt(x^2 +x +7 )= 5$ for x=-2
        have h3 : Real.sqrt ((-2 : ℝ) ^ 2 + (-2) + 7) = 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        nlinarith [h3]
    · -- x = 1
      constructor
      · norm_num
      · -- Show $x^2 +x + \sqrt(x^2 +x +7 )= 5$ for x=1
        have h3 : Real.sqrt ((1 : ℝ) ^ 2 + (1) + 7) = 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        nlinarith [h3]