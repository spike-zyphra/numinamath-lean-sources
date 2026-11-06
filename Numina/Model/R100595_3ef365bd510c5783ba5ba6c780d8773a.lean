import Mathlib

theorem algebra_283758 {a b c : ℝ} (habc : a ≠ b ∧ b ≠ c ∧ a ≠ c)
    (h : (b - a) ^ 2 - 4 * (b - c) * (c - a) = 0) :
    (b - c) / (c - a) = 1 := by
  have h1 : a ≠ b := habc.1
  have h2 : b ≠ c := habc.2.1
  have h3 : a ≠ c := habc.2.2

  have h_eq : (2 * c - (a + b)) ^ 2 = 0 := by
    nlinarith

  have h_eq2 : 2 * c - (a + b) = 0 := by
    rw [sq_eq_zero_iff] at h_eq
    exact h_eq

  have h_c : c = (a + b) / 2 := by
    linarith

  have num_eq : b - c = (b - a) / 2 := by
    rw [h_c]
    linarith

  have den_eq : c - a = (b - a) / 2 := by
    rw [h_c]
    linarith

  have h_ne : c - a ≠ 0 := by
    intro h_eq_zero
    have h_eq_a : c = a := by linarith
    have h_eq_a' : a = c := by linarith [h_eq_a]
    exfalso
    exact h3 (by linarith)

  rw [num_eq, den_eq]
  have h_bne : b - a ≠ 0 := by
    intro h_eq
    have h_eq' : b = a := by linarith
    have h_eq'' : a = b := by linarith [h_eq']
    exfalso
    exact h1 (by linarith)

  field_simp [h_bne, h_ne]
  <;> linarith