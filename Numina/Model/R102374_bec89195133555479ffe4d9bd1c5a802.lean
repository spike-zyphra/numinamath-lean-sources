import Mathlib

theorem algebra_237562 {a b : ℝ} (ha : (a + b) * (a ^ 2 - b ^ 2) = 4) (hb : (a - b) * (a ^ 2 + b ^ 2) = 5 / 2) :
    (a = 3 / 2 ∧ b = 1 / 2) ∨ (a = -1 / 2 ∧ b = -3 / 2) := by

  have h1 : (a + b) ^ 2 * (a - b) = 4 := by
    nlinarith

  have h2 : (a - b) * (a ^ 2 + b ^ 2) = 5 / 2 := hb

  have h3 : a ^ 2 + b ^ 2 = ((a + b) ^ 2 + (a - b) ^ 2) / 2 := by
    nlinarith

  rw [h3] at h2

  have h4 : (a - b) * ((a + b) ^ 2 + (a - b) ^ 2) = 5 := by
    nlinarith

  have h5 : (a - b) ^ 3 = 1 := by
    nlinarith [h1, h4]

  have h6 : a - b = 1 := by
    have h : (a - b) ^ 3 - 1 = 0 := by linarith
    have eq1 : (a - b - 1) * ((a - b) ^ 2 + (a - b) + 1) = 0 := by
      ring_nf at h ⊢
      linarith
    cases' (mul_eq_zero.mp eq1) with eq2 eq3
    · -- Case where (a - b - 1) = 0, so a - b = 1
      have h7 : a - b = 1 := by linarith
      linarith
    · -- Case where (a - b)^2 + (a - b) + 1 = 0
      have h7 : (a - b) ^ 2 + (a - b) + 1 = 0 := by linarith
      nlinarith [sq_nonneg ((a - b) + 1 / 2)]

  have h7 : (a + b) ^ 2 = 4 := by
    rw [show a - b = 1 by linarith [h6]] at h1
    nlinarith

  have h8 : a + b = 2 ∨ a + b = -2 := by
    have h9 : (a + b) ^ 2 = 4 := h7
    have : (a + b) ^ 2 - 4 = 0 := by linarith
    have h10 : ((a + b) - 2) * ((a + b) + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- Case where a + b - 2 = 0, so a + b = 2
      left
      linarith
    · -- Case where a + b + 2 = 0, so a + b = -2
      right
      linarith

  cases' h8 with h81 h82
  · -- Case where a + b = 2
    have h9 : a = 3 / 2 := by
      nlinarith [h6, h81]
    have h10 : b = 1 / 2 := by
      nlinarith [h6, h81]
    left
    exact ⟨h9, h10⟩
  · -- Case where a + b = -2
    have h9 : a = -1 / 2 := by
      nlinarith [h6, h82]
    have h10 : b = -3 / 2 := by
      nlinarith [h6, h82]
    right
    exact ⟨h9, h10⟩