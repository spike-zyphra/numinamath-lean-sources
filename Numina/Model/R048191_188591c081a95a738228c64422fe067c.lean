import Mathlib
open Real

theorem algebra_95809 (a b c : ℝ)
  (ha : a ≠ 0)      (hb : b ≠ 0)      (hc : c ≠ 0)
  (h1 : a = b * c)  (h2 : b = a * c)  (h3 : c = a * b)
: (a, b, c) = ( 1, 1, 1)
∨ (a, b, c) = ( 1,-1,-1)
∨ (a, b, c) = (-1,-1, 1)
∨ (a, b, c) = (-1, 1,-1) := by

  have eq1 : c ^ 2 = 1 := by
    have h4 : b = b * c ^ 2 := by
      calc
        b = a * c := by linarith
        _ = (b * c) * c := by rw [h1]
        _ = b * c ^ 2 := by ring
    have h5 : c ^ 2 = 1 := by
      apply (mul_left_inj' hb).mp
      linarith
    linarith

  have hc2 : c = 1 ∨ c = -1 := by
    rw [sq_eq_one_iff] at eq1
    exact eq1

  cases hc2 with
  | inl hc1 =>
    have h4 : a = b := by
      rw [hc1] at h1
      linarith
    have h5 : a ^ 2 = 1 := by
      rw [hc1] at h3
      have : a * b = 1 := by linarith [h4]
      have : a * a = 1 := by
        rw [show b = a by linarith [h4]] at this
        linarith
      linarith [this]
    have ha2 : a = 1 ∨ a = -1 := by
      have h6 : a ^ 2 - 1 = 0 := by linarith
      have h7 : (a - 1) * (a + 1) = 0 := by linarith
      cases (mul_eq_zero.1 h7) with
      | inl h8 =>
        left
        linarith
      | inr h9 =>
        right
        linarith

    cases ha2 with
    | inl ha1 =>
      have hb1 : b = 1 := by linarith [h4, ha1]
      left
      simp [ha1, hb1, hc1]
    | inr ha1 =>
      have hb1 : b = -1 := by linarith [h4, ha1]
      right
      right
      left
      simp [ha1, hb1, hc1]
  | inr hc2 =>
    have h4 : a = -b := by
      rw [hc2] at h1
      linarith
    have h5 : b ^ 2 = 1 := by
      rw [hc2] at h3
      have h11 : a * b = -1 := by linarith [h4]
      rw [show a = -b by linarith [h4]] at h11
      linarith
    have hb2 : b = 1 ∨ b = -1 := by
      have h6 : b ^ 2 - 1 = 0 := by linarith
      have h7 : (b - 1) * (b + 1) = 0 := by linarith
      cases (mul_eq_zero.1 h7) with
      | inl h8 =>
        left
        linarith
      | inr h9 =>
        right
        linarith
    cases hb2 with
    | inl hb1 =>
      have ha1 : a = -1 := by
        linarith [h4, hb1]
      have h7 : (a, b, c) = (-1, 1, -1) := by
        simp [ha1, hb1, hc2]
      right
      right
      right
      simp [h7]
    | inr hb1 =>
      have ha1 : a = 1 := by
        linarith [h4, hb1]
      have h7 : (a, b, c) = (1, -1, -1) := by
        simp [ha1, hb1, hc2]
      right
      left
      simp [h7]