import Mathlib

theorem algebra_239506 {x y z : ℝ} (h : x + y * z = 2 ∧ y + x * z = 2 ∧ z + x * y = 2) :
    (x = 1 ∧ y = 1 ∧ z = 1) ∨ (x = -2 ∧ y = -2 ∧ z = -2) := by
  rcases h with ⟨eq1, eq2, eq3⟩

  have eq4 : (y - x) * (1 - z) = 0 := by
    nlinarith
  have eq5 : (z - y) * (1 - x) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp eq4) with h6 h7

  · -- Case y - x = 0, so y = x
    have eq8 : y = x := by
      linarith
    have eq9 : (z - x) * (1 - x) = 0 := by
      have eq5' : (z - y) * (1 - x) = 0 := eq5
      rw [show y = x by linarith] at eq5'
      linarith

    cases' (mul_eq_zero.mp eq9) with h10 h11

    · -- Case z - x = 0, so z = x
      have eq12 : z = x := by
        linarith
      have eq13 : x ^ 2 + x - 2 = 0 := by
        have h14 : z = x := eq12
        have h15 : y = x := eq8
        rw [h14, h15] at eq1
        linarith
      have h17 : (x - 1) * (x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h17) with h18 h19
      · -- Case x - 1 = 0, so x = 1
        have hx1 : x = 1 := by linarith
        have hy1 : y = 1 := by
          linarith [eq8, hx1]
        have hz1 : z = 1 := by
          linarith [eq12, hx1]
        left
        exact ⟨hx1, hy1, hz1⟩
      · -- Case x + 2 = 0, so x = -2
        have hx2 : x = -2 := by linarith
        have hy2 : y = -2 := by
          linarith [eq8, hx2]
        have hz2 : z = -2 := by
          linarith [eq12, hx2]
        right
        exact ⟨hx2, hy2, hz2⟩

    · -- Case 1 - x = 0, so x = 1
      have hx1 : x = 1 := by linarith
      have eq14 : y = 1 := by 
        linarith [eq8, hx1]
      have eq15 : z = 1 := by 
        rw [show x = 1 by linarith, show y = 1 by linarith] at eq1
        linarith
      left
      exact ⟨hx1, eq14, eq15⟩

  · -- Case 1 - z = 0, so z = 1
    have h8 : z = 1 := by linarith
    have eq10 : x + y = 2 := by 
      have h8' : z = 1 := h8
      rw [h8'] at eq1
      linarith
    have eq12 : x * y = 1 := by
      have h8' : z = 1 := h8
      rw [h8'] at eq3
      linarith

    have eq13 : y = 2 - x := by 
      linarith [eq10]
    have eq14 : x * (2 - x) = 1 := by 
      rw [eq13] at eq12
      linarith
    have h10 : x ^ 2 - 2 * x + 1 = 0 := by
      linarith [eq14]
    have h9 : (x - 1) ^ 2 = 0 := by
      nlinarith [h10]
    have h11 : x - 1 = 0 := by 
      apply pow_eq_zero 
      exact h9
    have hx1 : x = 1 := by
      linarith [h11]
    have hy1 : y = 1 := by 
      rw [hx1] at eq13
      linarith [eq13]
    have hz1 : z = 1 := by
      linarith [h8]
    left
    exact ⟨hx1, hy1, hz1⟩