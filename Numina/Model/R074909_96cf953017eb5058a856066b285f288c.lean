import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_18685 (r : ℝ) (θ : ℝ) (h : r > 0) :
    r^2 * cos (2 * θ) = 4 ↔ ∃ x y, x = r * cos θ ∧ y = r * sin θ ∧ x^2 - y^2 = 4 := by
  constructor
  · -- Assume r^2 * cos(2θ) = 4, derive ∃ x y, x = r * cos θ ∧ y = r * sin θ ∧ x^2 - y^2 = 4
    intro hr
    have hcos : cos (2 * θ) = cos θ ^ 2 - sin θ ^ 2 := by
      rw [cos_two_mul, sin_sq, cos_sq]
      ring
    rw [hcos] at hr
    use r * cos θ, r * sin θ
    constructor
    · -- x = r * cos θ
      rfl
    constructor
    · -- y = r * sin θ
      rfl
    · -- x^2 - y^2 = 4
      have eqn : (r * cos θ)^2 - (r * sin θ)^2 = r^2 * (cos θ^2 - sin θ^2) := by
        ring_nf
      rw [eqn]
      linarith
  · -- Assume ∃ x y, x = r * cos θ ∧ y = r * sin θ ∧ x^2 - y^2 = 4, derive r^2 * cos(2θ) = 4
    rintro ⟨x, y, hr1, hr2, hxy⟩
    have hcos : cos (2 * θ) = cos θ ^ 2 - sin θ ^ 2 := by
      rw [cos_two_mul, sin_sq, cos_sq]
      ring
    rw [hcos]
    have eqn : x^2 - y^2 = r^2 * (cos θ^2 - sin θ^2) := by
      rw [hr1, hr2]
      ring_nf
    linarith [eqn, hxy]