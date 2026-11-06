import Mathlib

open Real

theorem calculus_145363 (u : ℝ → ℝ → ℝ → ℝ)
    (hu : u = fun x y z => x^3 * y^3 * z^3) (M : EuclideanSpace ℝ (Fin 3))
    (hM : M = ![1, 1, 1]) (v : EuclideanSpace ℝ (Fin 3))
    (hv : v = ![cos (π / 3), cos (π / 4), cos (π / 3)]) :
    deriv (fun t => u (M 0 + t * v 0) (M 1 + t * v 1) (M 2 + t * v 2)) 0 =
    3 / 2 * (2 + sqrt 2) := by
  rw [hu, hM, hv]
  simp [deriv_mul, deriv_pow, deriv_id'', mul_comm, Fin.sum_univ_three, add_mul, mul_add]
  all_goals
    norm_num [cos_pi_div_three, cos_pi_div_four] at *
  all_goals
    ring_nf <;> norm_num [sqrt_sq] <;> ring