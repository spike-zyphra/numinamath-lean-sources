import Mathlib
open Real

theorem algebra_89 : ∑ i ∈ Finset.range 2003, (1 / (sqrt (i + 1) + sqrt (i + 2))) = 2 * sqrt 501 - 1 := by
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / (sqrt (i + 1) + sqrt (i + 2))) = sqrt (n + 1) - 1 := by 
    intro n 
    induction n with 
    | zero =>
      simp
      <;> ring_nf <;> norm_num 
    | succ n ih => 
      rw [Finset.sum_range_succ, ih]
      field_simp [ add_mul, mul_add, pow_two, sub_eq_add_neg, mul_assoc ]
      <;> ring_nf <;> field_simp <;> ring
  specialize h1 2003
  have eq1 : ∑ i ∈ Finset.range 2003, (1 / (sqrt (i + 1) + sqrt (i + 2))) = sqrt (2003 + 1) - 1 := by 
    simpa using h1
  have h2 : sqrt (2003 + 1) = 2 * sqrt 501 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf 
    <;> norm_num
  have eq2 : sqrt (2003 + 1) - 1 = 2 * sqrt 501 - 1 := by 
    rw [h2]
  rw [eq1]
  all_goals norm_num at eq2 ⊢
  all_goals linarith [eq2, Real.sqrt_nonneg 501]