import Mathlib

theorem algebra_173861 (x y z : ℝ) (h1 : x + y - z = -1) (h2 : x^2 - y^2 + z^2 = 1) (h3 : -x^3 + y^3 + z^3 = -1) :
    (x = 1 ∧ y = -1 ∧ z = 1) ∨ (x = -1 ∧ y = -1 ∧ z = -1) := by

  have hz : z = x + y + 1 := by linarith
  rw [hz] at h2
  have eq1 : (x + y) * (x + 1) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp eq1) with h4 h5
  · -- Case where x + y = 0 
    have eq2 : y = -x := by linarith
    have eq3 : z = 1 := by
      rw [eq2] at hz
      linarith
    rw [eq2, eq3] at h3
    have eq4 : x^3 = 1 := by 
      nlinarith
    have eq5 : x = 1 := by 
      have h4 : x^3 - 1 = 0 := by linarith
      have h5 : (x - 1) * (x^2 + x + 1) = 0 := by 
        ring_nf at h4 ⊢
        linarith
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- Case x - 1 = 0 
        linarith
      · -- Case x^2 + x + 1 = 0
        nlinarith [sq_nonneg (x + 1 / 2)]
    left
    constructor
    · linarith
    constructor
    · linarith
    · linarith

  · -- Case where x + 1 = 0 
    have eq6 : x = -1 := by linarith
    have eq7 : z = y := by 
      rw [eq6] at hz
      linarith
    rw [eq6, show z = y by linarith [eq7] ] at h3
    have eq8 : y = -1 := by
      have h4 : y^3 = -1 := by
        nlinarith
      have h5 : y = -1 := by
        have h4' : y^3 + 1 = 0 := by linarith
        have h6 : (y + 1) * (y^2 - y + 1) = 0 := by
          ring_nf at h4' ⊢
          linarith
        cases' (mul_eq_zero.mp h6) with h7 h8
        · -- Case y + 1 = 0
          linarith
        · -- Case y^2 - y + 1 = 0
          nlinarith [sq_nonneg (y - 1 / 2)]
      linarith
    right
    constructor
    · linarith
    constructor
    · linarith
    · -- Show z = -1 
      linarith [eq7, eq8]