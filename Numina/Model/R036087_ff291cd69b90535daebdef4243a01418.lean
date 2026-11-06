import Mathlib

theorem algebra_1488 (a : ℝ) (ha : a > 0) (h : a^2 - 19 * a - 150 = 0) :
    ∑ i ∈ Finset.range 2000, (1 / (Real.sqrt (a + i) + Real.sqrt (a + i + 1))) = 40 := by 
  have ha25 : a = 25 := by 
    nlinarith 
  rw [ha25]
  have h2 : ∀ i : ℕ, 1 / (Real.sqrt (25 + (i : ℝ)) + Real.sqrt (25 + (i : ℝ) + 1)) =
    Real.sqrt (25 + (i : ℝ) + 1) - Real.sqrt (25 + (i : ℝ)) := by 
    intro i 
    have h1 : 0 < Real.sqrt (25 + (i : ℝ) + 1) + Real.sqrt (25 + (i : ℝ)) := by 
      positivity
    have h3 : Real.sqrt (25 + (i : ℝ) + 1) ^ 2 = (25 + (i : ℝ) + 1) := Real.sq_sqrt (show (0 : ℝ) ≤ 25 + (i : ℝ) + 1 by linarith)
    have h4 : Real.sqrt (25 + (i : ℝ)) ^ 2 = (25 + (i : ℝ)) := Real.sq_sqrt (show (0 : ℝ) ≤ 25 + (i : ℝ) by linarith)
    field_simp [h1]
    <;> nlinarith [Real.sqrt_nonneg (25 + (i : ℝ) + 1), Real.sqrt_nonneg (25 + (i : ℝ)), sq_nonneg (Real.sqrt (25 + (i : ℝ) + 1) - Real.sqrt (25 + (i : ℝ))), sq_nonneg (Real.sqrt (25 + (i : ℝ) + 1) + Real.sqrt (25 + (i : ℝ))), Real.mul_self_sqrt (show (0 : ℝ) ≤ 25 + (i : ℝ) + 1 by linarith), Real.mul_self_sqrt (show (0 : ℝ) ≤ 25 + (i : ℝ) by linarith)]
  have h3 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / (Real.sqrt (25 + (i : ℝ)) + Real.sqrt (25 + (i : ℝ) + 1))) = Real.sqrt (25 + (n : ℝ)) - Real.sqrt (25 : ℝ) := by 
    intro n 
    induction n with 
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [h2]
      <;> ring_nf <;> field_simp [Real.sqrt_nonneg (25 + (n : ℝ) + 1), Real.sqrt_nonneg (25 + (n : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 25 + (n : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 25 + (n : ℝ) + 1 by linarith)]
      <;> ring_nf <;> norm_num
      <;> ring 
  have h4 : ∑ i ∈ Finset.range 2000, (1 / (Real.sqrt (25 + (i : ℝ)) + Real.sqrt (25 + (i : ℝ) + 1))) = Real.sqrt (25 + (2000 : ℝ)) - Real.sqrt (25 : ℝ) := by 
    specialize h3 2000
    simpa using h3 
  rw [h4]
  have h5 : Real.sqrt (25 + (2000 : ℝ)) = (45 : ℝ) := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h6 : Real.sqrt (25 : ℝ) = (5 : ℝ) := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h5, h6]
  all_goals norm_num