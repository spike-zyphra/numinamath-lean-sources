import Mathlib

open Real

theorem calculus_307383 {f : ℝ → ℝ}
    (hf : f = fun x => (cos (x ^ 2 + π) ^ 2 + sin (x ^ 2) ^ 2) * cos (x ^ 3 + 2 * x)) :
    deriv f = fun x => -sin (x ^ 3 + 2 * x) * (3 * x ^ 2 + 2) := by
  rw [hf]
  funext x
  have h1 : cos (x ^ 2 + π) ^ 2 + sin (x ^ 2) ^ 2 = 1 := by
    have hcos : cos (x ^ 2 + π) = -cos (x ^ 2) := by
      rw [cos_add, cos_pi, sin_pi]
      ring
    rw [hcos]
    have h2 : (-cos (x ^ 2)) ^ 2 + sin (x ^ 2) ^ 2 = 1 := by
      have h3 : cos (x ^ 2) ^ 2 + sin (x ^ 2) ^ 2 = 1 := by
        exact cos_sq_add_sin_sq (x ^ 2)
      nlinarith
    exact h2
  simp [h1]
  all_goals
  simp [deriv_mul, deriv_pow, deriv_add, deriv_id'', mul_comm]
  <;> field_simp [cos_sq_add_sin_sq, Real.sin_sq, Real.cos_sq] <;> ring_nf <;> field_simp <;> ring