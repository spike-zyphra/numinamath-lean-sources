import Mathlib

open Real

theorem algebra_284106 {f : ℝ → ℝ} (hf : ∀ x, f x = x / sqrt (1 + x ^ 2)) :
    f^[99] 1 = 1 / 10 := by
  have f1 : ∀ (n : ℕ), f^[n] 1 = 1 / sqrt (↑n + 1 : ℝ) := by
    intro n
    induction n with
    | zero =>
      simp
      <;> norm_num [Real.sqrt_one]
    | succ n ih =>
      have h1 : f^[n + 1] 1 = f (f^[n] 1) := by
        simp [Function.iterate_succ_apply']
      rw [h1, ih]
      simp [hf]
      field_simp
      <;> ring_nf <;> field_simp [Real.sqrt_sq]
      <;> ring_nf <;> norm_num
  have h99 : f^[99] 1 = 1 / sqrt (↑(99 : ℕ) + 1 : ℝ) := f1 99
  rw [h99]
  have h2 : sqrt (↑(99 : ℕ) + 1 : ℝ) = (10 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h2]
  all_goals norm_num