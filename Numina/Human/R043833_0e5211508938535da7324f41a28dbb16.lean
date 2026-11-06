import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- 3. In the Cartesian coordinate system, $\vec{e}$ is a unit vector, and vector $\vec{a}$ satisfies $\vec{a} \cdot \vec{e}=2$, and $|\vec{a}|^{2} \leqslant 5|\vec{a}+t \vec{e}|$ for any real number $t$, then the range of $|\vec{a}|$ is $\qquad$ . -/
theorem algebra_206430 (e a : EuclideanSpace ℝ (Fin 2))
  (h₀ : ‖e‖ = 1) (h₁ : inner a e = (2: ℝ))
  (h₂ : ∀ t : ℝ, ‖a‖^2 ≤ 5 * ‖a + t • e‖) :
  ‖a‖ ∈ Set.Icc (√5) (2 * √5) := by
  -- first saure h₂ and transform inequality to 0 ≤ 25t^2 + 100t + (25‖a‖^2 - ‖a‖^4)
  have h₂ (t : ℝ) : 0 ≤ 25 * (t * t) + 100 * t + (25 * ‖a‖^2 - ‖a‖^4) := by
    have h := sq_le_sq₀ (by positivity) (by positivity) |>.mpr <| h₂ t
    ring_nf at h
    rw [norm_add_sq_real a (t • e)] at h
    rw [norm_smul, real_inner_smul_right, h₁, h₀] at h
    simp at h
    linarith
  -- quadratic equation always being nonegative means disriminant is nonnegative
  have h : discrim 25 100  (25 * ‖a‖^2 - ‖a‖^4) ≤ 0 := discrim_le_zero h₂
  dsimp [discrim] at h
  -- the discriminant condition becomes (2‖a‖^2 - 25)^2 ≤ 15^2, which means 10 ≤ 2 * ‖a‖^2 ≤ 40, which proves the final target
  have h : (2 * ‖a‖^2 - 25 ) ^2 ≤ 15^2 := by linarith [h]
  obtain ⟨h_lhs, h_rhs⟩ := abs_le_of_sq_le_sq' h (by positivity)
  constructor
  all_goals rw [← Real.sqrt_sq (show ‖a‖ ≥ 0 by positivity)]
  . apply sqrt_le_sqrt
    linarith only [h_lhs]
  . rw [show 2 = √(2^2) by simp, ← Real.sqrt_mul (by positivity)]
    apply sqrt_le_sqrt
    linarith only [h_rhs]