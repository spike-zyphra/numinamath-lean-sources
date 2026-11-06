import Mathlib

theorem algebra_177720 (x : ℝ) (hx : x ≠ 3) : (2 / (3 - x) + 1 / 2) = 6 / (x * (3 - x)) ↔ x = 4 := by
  constructor
  · -- Assume (2 / (3 - x) + 1 / 2) = 6 / (x * (3 - x)), prove x = 4
    intro h
    have h1 : x ≠ 3 := hx
    have h2 : x ≠ 0 := by
      by_contra h2
      rw [h2] at h
      norm_num [h1] at h
      all_goals norm_num at h
    have eq2 : 2 / (3 - x) + 1 / 2 = 6 / (x * (3 - x)) := h
    have eq4 : (2 / (3 - x) + 1 / 2) * (2 * x * (3 - x)) = 4 * x + x * (3 - x) := by
      have hne : 3 - x ≠ 0 := by
        intro h'
        apply hx
        linarith
      field_simp [hne, h2] at *
      ring
    have eq5 : (6 / (x * (3 - x))) * (2 * x * (3 - x)) = 12 := by
      have hne1 : x ≠ 0 := h2
      have hne2 : 3 - x ≠ 0 := by
        intro h'
        apply hx
        linarith
      have hne3 : x * (3 - x) ≠ 0 := by
        apply mul_ne_zero
        · exact h2
        · -- Show 3 - x ≠ 0
          intro h3
          have : x = 3 := by linarith
          tauto
      field_simp [hne1, hne2, hne3]
      ring
    have eq3 : (2 / (3 - x) + 1 / 2) * (2 * x * (3 - x)) = (6 / (x * (3 - x))) * (2 * x * (3 - x)) := by
      rw [eq2]
    rw [eq4, eq5] at eq3
    -- Now we have the polynomial equation.
    have eq6 : 4 * x + x * (3 - x) = 12 := by
      nlinarith
    -- Now solve the quadratic equation.
    have eq7 : x ^ 2 - 7 * x + 12 = 0 := by
      nlinarith
    -- Factor the quadratic.
    have eq8 : (x - 3) * (x - 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 eq8) with h9 h10
    · -- Case x - 3 = 0
      exfalso
      apply hx
      linarith
    · -- Case x - 4 = 0
      linarith
  · -- Assume x = 4, prove the equation
    intro h
    rw [h]
    norm_num