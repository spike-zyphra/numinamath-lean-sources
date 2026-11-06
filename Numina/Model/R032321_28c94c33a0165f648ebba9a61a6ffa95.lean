import Mathlib

open Polynomial

theorem algebra_231255 {n m : ℤ} {T : ℤ → ℝ[X]} (hT : T = Chebyshev.T ℝ) :
    ∀ x, (T n).eval ((T m).eval x) = (T m).eval ((T n).eval x) := by
  intro x
  rw [hT]
  have h1 : (Chebyshev.T ℝ n).comp ((Chebyshev.T ℝ m)) = (Chebyshev.T ℝ m).comp ((Chebyshev.T ℝ n)) := by
    rw [← Chebyshev.T_mul]
    rw [← Chebyshev.T_mul]
    all_goals ring_nf
  have h2 : ( (Chebyshev.T ℝ n).comp ((Chebyshev.T ℝ m)) ).eval x = ( (Chebyshev.T ℝ m).comp ((Chebyshev.T ℝ n)) ).eval x := by
    rw [h1]
  simp [Polynomial.eval_comp] at h2 ⊢
  <;> linarith