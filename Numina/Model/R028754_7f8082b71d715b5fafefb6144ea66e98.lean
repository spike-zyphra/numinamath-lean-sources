import Mathlib

theorem algebra_612 {x y z : ℝ} (h1 : (x + y) * (z + 1) = 24) (h2 : (x + z) * (y + 1) = 24) (h3 : (y + z) * (x + 1) = 24) :
    (x = 3 ∧ y = 3 ∧ z = 3) ∨ (x = -4 ∧ y = -4 ∧ z = -4) ∨ (x = 11 ∧ y = 1 ∧ z = 1) ∨ (x = 1 ∧ y = 11 ∧ z = 1) ∨ (x = 1 ∧ y = 1 ∧ z = 11) := by
  have h4 : (z - y) * (x - 1) = 0 := by
    nlinarith

  cases (mul_eq_zero.mp h4) with
  | inl h5 =>
    have h51 : z = y := by linarith
    have eq1 : y * (x + 1) = 12 := by
      rw [show z = y by linarith] at h3
      nlinarith
    have eq2 : x + y ^ 2 = 12 := by
      have h_eq : (x + y) * (y + 1) = 24 := by
        rw [show z = y by linarith] at h1
        linarith
      nlinarith
    have h_eq3 : (y - 1) * (x - y) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h_eq3) with
    | inl h_eq4 =>
      have hy1 : y = 1 := by linarith
      have hx11 : x = 11 := by
        rw [hy1] at eq1
        nlinarith
      have hz1 : z = 1 := by
        linarith [h51, hy1]
      simp [hx11, hy1, hz1]
    | inr h_eq5 =>
      have h_eq6 : x = y := by linarith
      have h_eq7 : y ^ 2 + y - 12 = 0 := by
        rw [show x = y by linarith] at eq1
        nlinarith
      have h_eq8 : (y + 4) * (y - 3) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h_eq8) with
      | inl h_eq9 =>
        have hy1 : y = -4 := by linarith
        have hx1 : x = -4 := by
          nlinarith [h_eq6, hy1]
        have hz1 : z = -4 := by
          linarith [h51, hy1]
        simp [hx1, hy1, hz1]
      | inr h_eq10 =>
        have hy1 : y = 3 := by linarith
        have hx1 : x = 3 := by
          nlinarith [h_eq6, hy1]
        have hz1 : z = 3 := by
          linarith [h51, hy1]
        simp [hx1, hy1, hz1]
  | inr h6 =>
    have hx1 : x = 1 := by
      linarith
    have h_eq1 : y + z = 12 := by
      rw [show x = 1 by linarith] at h3
      nlinarith
    have h_eq2 : y * z = 11 := by
      rw [show x = 1 by linarith] at h1 h2
      nlinarith
    have h_eq3 : (y - 11) * (y - 1) = 0 := by
      have h_eq4 : y + z = 12 := h_eq1
      have h_eq5 : y * z = 11 := h_eq2
      have h_eq6 : z = 12 - y := by linarith
      rw [h_eq6] at h_eq5
      nlinarith
    cases (mul_eq_zero.mp h_eq3) with
    | inl h_eq4 =>
      have hy1 : y = 11 := by linarith
      have hz1 : z = 1 := by
        nlinarith
      simp [hx1, hy1, hz1]
    | inr h_eq5 =>
      have hy1 : y = 1 := by linarith
      have hz1 : z = 11 := by
        nlinarith
      simp [hx1, hy1, hz1]