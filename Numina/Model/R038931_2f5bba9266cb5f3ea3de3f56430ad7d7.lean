import Mathlib

open Real

theorem algebra_191268 {f : ℝ → ℝ} (hf : f = fun x => x / sqrt (1 + x ^ 2)) (n : ℕ) :
    f^[n] = fun x => x / sqrt (1 + n * x ^ 2) := by
  funext x
  have h1 : ∀ (n : ℕ), f^[n] x = x / sqrt (1 + (↑n : ℝ) * x ^ 2) := by
    intro n
    induction n with
    | zero =>
      simp [Function.iterate_zero_apply]
      <;> field_simp
    | succ n ih =>
      have eq1 : f^[n + 1] x = f (f^[n] x) := by
        simp [Function.iterate_succ_apply']
      rw [eq1]
      rw [ih]
      simp [hf]
      <;> field_simp
      <;> ring_nf <;> field_simp <;> ring_nf
  simpa using h1 n