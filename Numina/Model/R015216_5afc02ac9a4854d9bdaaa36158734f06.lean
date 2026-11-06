import Mathlib

theorem algebra_242628 {x y z : ℝ} (h1 : x^2 = (y - z)^2 - 8) (h2 : y^2 = (z - x)^2 - 16)
    (h3 : z^2 = (x - y)^2 + 32) :
    (x = -1 ∧ y = -3 ∧ z = -6) ∨ (x = 1 ∧ y = 3 ∧ z = 6) := by
  have h4 : z = 6 * x := by
    nlinarith [sq_nonneg (x + y - z), sq_nonneg (y - x), sq_nonneg (z - y)]
  have h5 : y = 3 * x := by
    nlinarith [sq_nonneg (x + y - z), sq_nonneg (y - x), sq_nonneg (z - y)]
  have h6 : x^2 = 1 := by
    rw [show y = 3 * x by linarith [h5], show z = 6 * x by linarith [h4]] at h1
    ring_nf at h1
    nlinarith
  have h7 : x = 1 ∨ x = -1 := by
    cases (sq_eq_one_iff.mp h6) with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith
  cases h7 with
  | inl hx1 =>
    have hy3 : y = 3 := by
      rw [h5]
      linarith [hx1]
    have hz6 : z = 6 := by
      rw [h4]
      linarith [hx1]
    right
    constructor
    · linarith [hx1]
    constructor
    · linarith [hy3]
    · linarith [hz6]
  | inr hx2 =>
    have hy3 : y = -3 := by
      rw [h5]
      linarith [hx2]
    have hz6 : z = -6 := by
      rw [h4]
      linarith [hx2]
    left
    constructor
    · linarith [hx2]
    constructor
    · linarith [hy3]
    · linarith [hz6]