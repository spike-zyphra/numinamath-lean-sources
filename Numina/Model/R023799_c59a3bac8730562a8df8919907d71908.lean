import Mathlib

open Real

theorem algebra_11592 {f : ℝ → ℝ} (hf : ∀ x, f x = x / sqrt (1 + x ^ 2)) :
    f^[99] 1 = 1 / 10 := by
  have f_eq : ∀ x, f x = x / sqrt (1 + x^2) := hf

  have induction_hypothesis : ∀ (n : ℕ), f^[n] 1 = 1 / sqrt (↑n + 1) := by
    intro n
    induction n with
    | zero =>
      simp
      <;> norm_num [Real.sqrt_eq_iff_sq_eq]
    | succ n ih =>
      have h1 : f^[n+1] 1 = f (f^[n] 1) := by
        simp [Function.iterate_succ_apply']
      rw [h1]
      rw [ih]
      field_simp [f_eq]
      <;> ring_nf <;> field_simp
      <;> ring_nf <;> norm_num [Real.sqrt_eq_iff_sq_eq]
      <;> norm_num [Real.sqrt_eq_iff_sq_eq]
  have h99 : f^[99] 1 = 1 / sqrt (↑(99 : ℕ) + 1) := induction_hypothesis 99
  rw [h99]
  have h2 : sqrt (↑(99 : ℕ) + 1) = 10 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> linarith
  rw [h2]
  all_goals
    ring_nf <;> norm_num
    <;> linarith
    <;> ring_nf <;> norm_num
    <;> linarith