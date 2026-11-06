import Mathlib

theorem algebra_219926 (a r : ℤ) (h₀ : a = 8) (h₁ : r ≠ 0)
    (h₂ : 5832 = a * r ^ 6) :
    a * r ^ 4 = 648 := by
  rw [h₀] at h₂ ⊢
  have h3 : r^6 = 729 := by
    nlinarith
  have h4 : r = 3 ∨ r = -3 := by
    have h5 : r^6 = 729 := h3
    have h6 : r^6 - 729 = 0 := by
      rw [h5]
      all_goals ring
    have h7 : (r^3 - 27) * (r^3 + 27) = 0 := by
      ring_nf at h6 ⊢
      linarith
    cases (mul_eq_zero.mp h7) with
    | inl h8 =>
      have h8' : r^3 = 27 := by linarith
      have h9 : r = 3 := by
        have h10 : r^3 - 27 = 0 := by linarith
        have h12 : r^3 - 27 = (r - 3) * (r^2 + 3 * r + 9) := by ring
        rw [h12] at h10
        cases (mul_eq_zero.mp h10) with
        | inl h13 =>
          linarith
        | inr h14 =>
          nlinarith [sq_nonneg (r + 1)]
      tauto
    | inr h8 =>
      have h9' : r^3 = -27 := by linarith
      have h10 : r = -3 := by
        have h11 : r^3 + 27 = 0 := by linarith
        have h12 : r^3 + 27 = (r + 3) * (r^2 - 3 * r + 9) := by ring
        rw [h12] at h11
        cases (mul_eq_zero.mp h11) with
        | inl h13 =>
          linarith
        | inr h14 =>
          nlinarith [sq_nonneg (r - 1)]
      tauto
  cases h4 with
  | inl h5 =>
    rw [h5]
    norm_num
  | inr h5 =>
    rw [h5]
    norm_num