import Mathlib

theorem algebra_195230 {a u : ℝ} (ha : a ≠ 0) (hu : u ≠ 0)
    (h1 : 3 / a + 1 / u = 7 / 2) (h2 : 2 / a - 3 / u = 6) :
    a = 2 / 3 := by
  have eq1 : 3 * u + a = 7 / 2 * a * u := by
    have h1' : 3 / a + 1 / u = 7 / 2 := h1
    field_simp [ha, hu] at h1' ⊢
    linarith
  have eq2 : 2 * u - 3 * a = 6 * a * u := by
    have h2' : 2 / a - 3 / u = 6 := h2
    field_simp [ha, hu] at h2' ⊢
    linarith
  have eq3 : 7 * a * u - 6 * u - 2 * a = 0 := by
    nlinarith [eq1]
  have eq4 : -6 * a * u + 2 * u - 3 * a = 0 := by
    nlinarith [eq2]
  have h3 : u = -1 := by
    have h4 : u = 0 ∨ u = -1 := by
      have eq5 : -22 * u * (u + 1) = 0 := by
        nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show u ≠ 0 by exact hu), eq3, eq4]
      cases' (mul_eq_zero.mp eq5) with h6 h7
      · -- -22 * u = 0, so u = 0
        left
        linarith
      · -- u + 1 = 0, so u = -1
        right
        linarith
    cases' h4 with h5 h8
    · -- u = 0, which is false
      contradiction
    · -- u = -1
      exact h8
  have h4 : a = 2 / 3 := by
    rw [show u = -1 by linarith [h3]] at eq3
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha)]
  linarith [h4]