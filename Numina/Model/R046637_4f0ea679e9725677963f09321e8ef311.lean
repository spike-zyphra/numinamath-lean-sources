import Mathlib

theorem algebra_108 : {(x, y) : ℝ×ℝ | y = x^2 - 4 * x ∧ x = y ∧ x ≠ 0} = {(5, 5)} := by
  ext ⟨x, y⟩
  simp [-mul_add, -add_mul]
  constructor
  · -- Assume ⟨x, y⟩ is in the left side set, prove it is in the right side set
    rintro ⟨h_eq1, h_eq2, h_ne⟩
    have h_eq3 : x = x^2 - 4 * x := by
      have h_sub : y = x := by linarith [h_eq2]
      rw [h_sub] at h_eq1
      linarith
    have h_eq4 : x^2 - 5 * x = 0 := by
      nlinarith
    have h_eq5 : x * (x - 5) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h_eq5) with h_eq6 h_eq7
    · -- Case x = 0, but we have x ≠ 0, so it's a contradiction
      exfalso
      tauto
    · -- Case x - 5 = 0, so x = 5
      have h_x5 : x = 5 := by linarith
      have h_y5 : y = 5 := by 
        nlinarith [h_eq2, h_x5]
      simp [h_x5, h_y5]
  · -- Assume ⟨x, y⟩ is in the right side set, prove it is in the left side set
    rintro (⟨rfl, rfl⟩)
    constructor
    · -- Check that the point (5,5) satisfies the equation y = x^2 - 4 x
      norm_num
    constructor
    · -- Check that x = y for the point (5, 5)
      norm_num
    · -- Check that x ≠ 0 for the point (5, 5)
      norm_num