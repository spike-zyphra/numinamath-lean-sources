import Mathlib

theorem calculus_155524 (f : ℝ → ℝ) (hf : f = fun x => x^3 * Real.sin x) :
    ∀ x, deriv f x = 3 * x^2 * Real.sin x + x^3 * Real.cos x := by
  intro x
  rw [hf]
  simp [deriv_mul, deriv_pow, Real.deriv_sin]
  all_goals ring_nf
  <;> field_simp
  <;> ring