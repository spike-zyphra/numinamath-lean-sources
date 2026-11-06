import Mathlib

open Real

theorem algebra_279335 {f : ℝ → ℝ} (hf : f = fun x => x / sqrt (1 + x ^ 2)) :
    f^[99] 1 = 1 / 10 := by
  have f1 : ∀ (n : ℕ), f^[n] 1 = 1 / Real.sqrt (↑n + 1) := by
    intro n
    induction n with
    | zero =>
      simp
      <;> norm_num
      <;> field_simp [hf]
      all_goals norm_num
    | succ n ih =>
      have h1 : f^[n + 1] 1 = f (f^[n] 1) := by
        simp [Function.iterate_succ_apply']
      rw [h1]
      rw [ih]
      field_simp [hf, show (↑n + 1 : ℝ) ≥ 0 by positivity, show (↑n + 2 : ℝ) ≥ 0 by positivity]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [Real.sqrt_nonneg, Real.sq_sqrt, mul_comm, mul_assoc]
      <;> ring_nf
      <;> norm_num
      all_goals try { tauto }
      all_goals try { positivity }
  have eq1 := f1 99
  rw [eq1]
  have h3 : Real.sqrt (↑(99 : ℕ) + 1) = (10 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [h3]
  all_goals norm_num
  all_goals try { positivity }