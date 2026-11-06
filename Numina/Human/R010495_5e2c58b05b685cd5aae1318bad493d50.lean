import Mathlib

theorem algebra_234539 (a b c : ℝ) (ha : a^3 - 2022 * a^2 + 1011 = 0) (hb : b^3 - 2022 * b^2 + 1011 = 0) (hc : c^3 - 2022 * c^2 + 1011 = 0) (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    1 / (a * b) + 1 / (b * c) + 1 / (a * c) = -2 := by 
  obtain ⟨h1,h2,h3⟩ := hne

  have eq_a : a^3 - 2022 * a^2 + 1011 = 0 := ha
  have eq_b : b^3 - 2022 * b^2 + 1011 = 0 := hb
  have eq_c : c^3 - 2022 * c^2 + 1011 = 0 := hc

  have h4 : a^2 + a * b + b^2 = 2022 * (a + b) := by
    have h : a^3 - 2022 * a^2 + 1011 - (b^3 - 2022 * b^2 + 1011) = 0 := by
      linarith [eq_a, eq_b]
    have : (a - b) * (a^2 + a * b + b^2 - 2022 * (a + b)) = 0 := by
      ring_nf at h ⊢
      linarith
    have h5 : a - b ≠ 0 := sub_ne_zero.mpr h1
    have : a^2 + a * b + b^2 - 2022 * (a + b) = 0 := by
      apply_fun (λ x => x / (a - b)) at this
      field_simp [h5] at this
      linarith
    linarith

  have h5 : a^2 + a * c + c^2 = 2022 * (a + c) := by
    have h : a^3 - 2022 * a^2 + 1011 - (c^3 - 2022 * c^2 + 1011) = 0 := by
      linarith [eq_a, eq_c]
    have : (a - c) * (a^2 + a * c + c^2 - 2022 * (a + c)) = 0 := by
      ring_nf at h ⊢
      linarith
    have h6 : a - c ≠ 0 := sub_ne_zero.mpr h2
    have : a^2 + a * c + c^2 - 2022 * (a + c) = 0 := by
      apply_fun (λ x => x / (a - c)) at this
      field_simp [h6] at this
      linarith
    linarith

  have h6 : b^2 + b * c + c^2 = 2022 * (b + c) := by
    have h : b^3 - 2022 * b^2 + 1011 - (c^3 - 2022 * c^2 + 1011) = 0 := by
      linarith [eq_b, eq_c]
    have : (b - c) * (b^2 + b * c + c^2 - 2022 * (b + c)) = 0 := by
      ring_nf at h ⊢
      linarith
    have h7 : b - c ≠ 0 := sub_ne_zero.mpr h3
    have : b^2 + b * c + c^2 - 2022 * (b + c) = 0 := by
      apply_fun (λ x => x / (b - c)) at this
      field_simp [h7] at this
      linarith
    linarith

  have h7 : a ≠ 0 := by
    by_contra h
    rw [h] at eq_a
    nlinarith

  have h8 : b ≠ 0 := by
    by_contra h
    rw [h] at eq_b
    nlinarith

  have h9 : c ≠ 0 := by
    by_contra h
    rw [h] at eq_c
    nlinarith
  -- just vieta theorem
  have h10 : a + b + c = 2022 := by 
    have eq1 : a^2 + a * b + b^2 = 2022 * (a + b) := h4
    have eq2 : a^2 + a * c + c^2 = 2022 * (a + c) := h5
    have eq3 : b^2 + b * c + c^2 = 2022 * (b + c) := h6

    have h11 : (c - b) * (a + b + c - 2022) = 0 := by
      nlinarith [h4, h5, h6]
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- c - b = 0, which is false since b ≠ c
      exfalso
      exact h3 (by linarith)
    · -- a + b + c - 2022 = 0
      linarith
  -- vieta theorem
  have h11 : a * b + b * c + c * a = 0 := by 
    have eq1 : a^2 + a * b + b^2 = 2022 * (a + b) := h4
    have eq2 : a^2 + a * c + c^2 = 2022 * (a + c) := h5
    have eq3 : b^2 + b * c + c^2 = 2022 * (b + c) := h6

    nlinarith [h10, h4, h5, h6]
  -- vieta theorem
  have h12 : a * b * c = -1011 := by
    have h14 : a^3 + b^3 + c^3 = 2022 * (a^2 + b^2 + c^2) - 3 * 1011 := by
      have eq1 : a^3 = 2022 * a^2 - 1011 := by nlinarith [eq_a]
      have eq2 : b^3 = 2022 * b^2 - 1011 := by nlinarith [eq_b]
      have eq3 : c^3 = 2022 * c^2 - 1011 := by nlinarith [eq_c]
      nlinarith [eq1, eq2, eq3]

    have h15 : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + b * c + c * a)) := by
      ring

    rw [h10, h11] at h15

    have h16 : a^2 + b^2 + c^2 = (a + b + c) ^ 2 - 2 * (a * b + b * c + c * a) := by
      ring

    rw [h10, h11] at h16

    nlinarith [h14, h15, h16]

  have h13 : 1 / (a * b) + 1 / (b * c) + 1 / (a * c) = -2 := by
    have h14 : a * b ≠ 0 := mul_ne_zero (by assumption) (by assumption)
    have h15 : b * c ≠ 0 := mul_ne_zero (by assumption) (by assumption)
    have h16 : a * c ≠ 0 := mul_ne_zero (by assumption) (by assumption)

    field_simp [h14, h15, h16, h7, h8, h9]
    nlinarith [h10, h12]

  exact h13