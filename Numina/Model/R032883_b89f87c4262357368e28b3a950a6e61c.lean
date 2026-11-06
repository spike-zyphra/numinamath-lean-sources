import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_235443 (f : ℝ → ℝ) (hf : f = sin) :
    ∀ x ∈ Icc 0 Real.pi, deriv (deriv f) x ≤ 0 := by
  intro x hx
  rw [hf]
  rcases hx with ⟨hx1, hx2⟩
  simp [deriv_const, deriv_id', Real.deriv_sin, Real.deriv_cos]
  have h1 : 0 ≤ sin x := by
    apply sin_nonneg_of_nonneg_of_le_pi
    all_goals linarith [Real.pi_pos, hx1, hx2]
  all_goals nlinarith [h1, hx1, hx2, Real.sin_nonneg_of_nonneg_of_le_pi (show (0 : ℝ) ≤ x by linarith) (show x ≤ Real.pi by linarith)]