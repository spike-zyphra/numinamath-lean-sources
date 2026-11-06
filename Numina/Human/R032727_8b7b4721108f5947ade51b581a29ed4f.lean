import Mathlib
open Real Set
open scoped BigOperators


/-
  Determine the smallest positive period of the function $y=(\sin x+\cos x)^{2}$.
-/
theorem algebra_9067 {f : ℝ → ℝ} (hf : f = λ x => (sin x + cos x)^2) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi) :=
by
  simp_all [IsLeast, lowerBounds]
  constructor
  · -- First, show π is a positive period of f
    constructor
    · exact pi_pos
    · ext x; ring
  · -- Second, show π is minimum positive period
    intro r rpos rperiod
    -- Transform the equality f x = f (x + r) to get sin (2 * x) = sin (2 * x + 2 * r)
    have rperiod' : ∀ x, (sin x + cos x) ^ 2 = (sin (x + r) + cos (x + r)) ^ 2 := by
      apply congrFun rperiod
    have transform_triangle : ∀ x, (sin x + cos x) ^ 2 = 1 + sin (2 * x) := by
      intro x
      have : (sin x + cos x) ^ 2 = (sin x) ^ 2 + (cos x) ^ 2 + 2 * sin x * cos x := by ring
      simp [this, sin_two_mul]
    have rperiod'' : ∀ x, sin (2 * x) = sin (2 * x + 2 * r) := by
      intro x
      have := rperiod' x
      rw [transform_triangle x, transform_triangle (x + r), mul_add] at this
      field_simp at this
      exact this
    -- Now consider the special value at x = π / 4, we show sin (π / 2 + 2 * r) = 1
    have hr := rperiod'' (π / 4)
    have : 2 *( π / 4) = π / 2 := by field_simp; ring
    rw [this] at hr
    field_simp at hr
    have : (π + 2 * r * 2) / 2 = π / 2 + 2 * r := by field_simp
    rw [this] at hr
    -- sin x = 1 implies x = π / 2 + 2 * k * π, so we derive 2 * r = 2 * n * π for some n
    have ⟨n, two_r_eq_two_n_pi⟩ := Real.sin_eq_one_iff.mp hr.symm
    simp at two_r_eq_two_n_pi
    have r_eq_n_pi : r = n * π := by
      rw [← mul_assoc] at two_r_eq_two_n_pi
      nth_rw 2 [mul_comm] at two_r_eq_two_n_pi
      rw [mul_assoc] at two_r_eq_two_n_pi
      linarith
    -- Now we have r = n * π. By case analysis, n cannoe be ≤ 0, so n ≥ 1, then r ≥ π.
    rcases le_or_gt n 0 with h | h
    · have : r ≤ 0 := by
        have nle0 : (n : ℝ) ≤ 0 := by exact Int.cast_nonpos.mpr h
        have πge0 : π ≥ 0 := pi_nonneg
        have : n * π ≤ 0 := mul_nonpos_of_nonpos_of_nonneg nle0 πge0
        linarith
      linarith
    · have : n ≥ 1 := by exact h
      have : (n : ℝ) ≥ 1 := by exact Int.cast_one_le_of_pos h
      rw [r_eq_n_pi]
      have πge0 : π ≥ 0 := pi_nonneg
      exact le_mul_of_one_le_left πge0 this
