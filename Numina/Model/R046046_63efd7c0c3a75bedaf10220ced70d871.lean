import Mathlib

open Real

theorem algebra_264285 : ∑ i ∈ Finset.range 2016, (1 / ((i + 1) * sqrt (i + 2) + (i + 2) * sqrt (i + 1))) = 1 - 1 / sqrt 2017 := by
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / ((i + 1) * sqrt (i + 2) + (i + 2) * sqrt (i + 1))) = 1 - 1 / sqrt (n + 1 : ℝ) := by 
    intro n 
    induction n with 
    | zero => 
      simp 
      <;> norm_num 
      <;> field_simp 
      <;> norm_num 
      <;> linarith 
    | succ n ih => 
      rw [Finset.sum_range_succ, ih] 
      field_simp 
      <;> ring_nf <;> field_simp [Real.sqrt_nonneg, Real.mul_self_sqrt, mul_self_sqrt, Real.sq_sqrt, mul_add, add_mul, pow_two, mul_comm, mul_left_comm] 
      <;> ring_nf <;> norm_num 
      <;> ring
  specialize h1 2016 
  norm_num at h1 ⊢
  <;> linarith 
  <;> norm_num 
  <;> linarith 
  <;> ring 
  <;> norm_num 
  <;> nlinarith