import Mathlib

open Real

theorem algebra_1874 : ∑ i ∈ Finset.range 99, (1 / (sqrt (i + 1) + sqrt (i + 2))) = 9 := by
  have h1 : ∀ (i : ℕ), (1 / (sqrt (i + 1) + sqrt (i + 2)) : ℝ) = sqrt (i + 2) - sqrt (i + 1) := by
    intro i
    have h2 : sqrt (i + 1) + sqrt (i + 2) ≠ 0 := by
      have h11 : sqrt (i + 1) ≥ 0 := Real.sqrt_nonneg (i + 1)
      have h12 : sqrt (i + 2) ≥ 0 := Real.sqrt_nonneg (i + 2)
      by_contra h
      have h3 : sqrt (i + 1) = 0 := by linarith [h11, h12, h]
      have h4 : (i + 1 : ℝ) = 0 := by
        rw [Real.sqrt_eq_zero (by linarith)] at h3
        linarith
      have h5 : (i : ℝ) = -1 := by
        linarith
      have h6 : i = 0 := by
        have h7 : (i : ℝ) ≥ 0 := by exact_mod_cast show (i : ℝ) ≥ 0 by positivity
        nlinarith
      linarith [h5, h6]
    
    have h3 : (1 / (sqrt (i + 1) + sqrt (i + 2)) : ℝ) = sqrt (i + 2) - sqrt (i + 1) := by
      have hx1 : (sqrt (i + 1) + sqrt (i + 2)) ≠ 0 := h2
      field_simp [hx1]
      <;> nlinarith [Real.sqrt_nonneg (i + 1), Real.sqrt_nonneg (i + 2),
          Real.sq_sqrt (show (0 : ℝ) ≤ (i + 1 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (i + 2 : ℝ) by nlinarith)]
    
    linarith
  have h2 : ∑ i in Finset.range 99, (1 / (sqrt (i + 1) + sqrt (i + 2)) : ℝ) =
      ∑ i in Finset.range 99, (sqrt (i + 2) - sqrt (i + 1) : ℝ) := by 
    apply Finset.sum_congr 
    · rfl
    · intro i hi
      specialize h1 i 
      simpa using h1
  
  rw [h2]
  
  have h3 : ∑ i in Finset.range 99, (sqrt (i + 2) - sqrt (i + 1) : ℝ) =
      sqrt (99 + 1 : ℝ) - sqrt (0 + 1 : ℝ) := by 
    have h4 : ∀ (n : ℕ), ∑ i in Finset.range n, (sqrt (i + 2) - sqrt (i + 1) : ℝ) = sqrt ((n : ℝ) + 1) - sqrt (1 : ℝ) := by 
      intro n
      induction n with
      | zero =>
        simp 
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        <;> field_simp [Real.sqrt_nonneg]
        <;> ring_nf 
        all_goals norm_num 
    specialize h4 99 
    rw [h4] 
    all_goals norm_num
  rw [h3] 
  have h4 : sqrt ((99 + 1 : ℝ)) = (10 : ℝ) := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
  have h5 : sqrt ((0 + 1 : ℝ)) = (1 : ℝ) := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
  rw [h4, h5] 
  all_goals norm_num