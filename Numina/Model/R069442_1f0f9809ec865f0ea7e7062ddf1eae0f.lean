import Mathlib

theorem algebra_166941 {p q : ℝ} (hp : p > 0) (hq : q > 0)
    (hroots : ∃ x y, x ≠ y ∧ x^2 + p * x + q = 0 ∧ y^2 + p * y + q = 0 ∧ |x - y| = 1) :
    p = Real.sqrt (4 * q + 1) := by

  rcases hroots with ⟨x, y, hxy, hx, hy, habs⟩

  have h1 : (x - y) ^ 2 = 1 := by
    cases eq_or_eq_neg_of_abs_eq habs with
    | inl h =>
      nlinarith
    | inr h =>
      nlinarith

  have h2 : x + y = -p := by
    have h3 : x^2 + p * x + q = 0 := hx
    have h4 : y^2 + p * y + q = 0 := hy

    have h5 : x^2 + p * x + q - (y^2 + p * y + q) = 0 := by
      linarith

    have h6 : (x - y) * (x + y + p) = 0 := by
      ring_nf at h5 ⊢
      linarith

    cases (mul_eq_zero.mp h6) with
    | inl h7 =>
      exfalso
      exact hxy (by linarith)
    | inr h8 =>
      linarith

  have h7 : (x * y) = q := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.2 hxy), hx, hy, h2]

  have h8 : p ^ 2 - 4 * q = 1 := by
    nlinarith [h1, h2, h7]

  have hp2 : p ^ 2 = 4 * q + 1 := by
    linarith

  have hp_eq : p = Real.sqrt (4 * q + 1) := by
    have hge : (4 * q + 1) ≥ 0 := by nlinarith
    have hsq : p ^ 2 = 4 * q + 1 := hp2
    have hp_pos : p > 0 := hp
    have hsqrt : p = Real.sqrt (4 * q + 1) := by
      rw [← hsq]
      field_simp [Real.sqrt_sq, hp_pos]
    exact hsqrt

  exact hp_eq