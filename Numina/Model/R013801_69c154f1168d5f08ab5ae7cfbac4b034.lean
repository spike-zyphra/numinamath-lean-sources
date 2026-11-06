import Mathlib

theorem algebra_187680 (x : ℝ) (hx : x ≠ 1 ∧ x ≠ -1) :
    1 / (1 - x) + 1 / (1 + x) + 2 / (1 + x ^ 2) + 4 / (1 + x ^ 4) + 8 / (1 + x ^ 8) = 16 / (1 - x ^ 16) := by

  rcases hx with ⟨hx1, hx2⟩
  have h1 : x - 1 ≠ 0 := by
    intro h
    apply hx1
    linarith

  have h2 : x + 1 ≠ 0 := by
    intro h
    apply hx2
    linarith

  have h3 : 1 - x ≠ 0 := by
    intro h
    apply hx1
    linarith

  have h4 : 1 + x ≠ 0 := by
    intro h
    apply hx2
    linarith

  have h5 : 1 + x ^ 2 ≠ 0 := by
    by_contra h
    have h11 : x ^ 2 = -1 := by linarith
    have h12 : x ^ 2 ≥ 0 := sq_nonneg x
    linarith

  have h6 : 1 + x ^ 4 ≠ 0 := by
    by_contra h
    have h11 : x ^ 4 = -1 := by linarith
    have h12 : x ^ 4 ≥ 0 := by positivity
    linarith

  have h7 : 1 + x ^ 8 ≠ 0 := by
    by_contra h
    have h11 : x ^ 8 = -1 := by linarith
    have h12 : x ^ 8 ≥ 0 := by positivity
    linarith

  have h8 : 1 - x ^ 16 ≠ 0 := by
    by_contra h
    have h9 : x ^ 16 = 1 := by linarith

    have h10 : x ^ 2 = 1 := by
      have h11 : x ^ 16 = 1 := h9
      have h12 : x ^ 16 - 1 = 0 := by linarith
      have h13 : x ^ 16 - 1 = (x ^ 2 - 1) * (x ^ 2 + 1) * (x  ^ 4 + 1) * (x ^ 8 + 1) := by ring
      rw [h13] at h12
      cases' (mul_eq_zero.mp h12) with h10a h10b
      cases' (mul_eq_zero.mp h10a) with h10c h10d
      cases' (mul_eq_zero.mp h10c) with h10e h10f
      · -- Case x^2 - 1 = 0
        linarith
      · -- Case x^2 + 1 = 0
        nlinarith [sq_nonneg (x ^ 2)]
      · -- Case x^4 + 1 = 0
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 4)]
      · -- Case x^8 + 1 = 0
        nlinarith [sq_nonneg (x ^ 4), sq_nonneg (x ^ 2), sq_nonneg (x ^ 8)]

    have h12 : x = 1 ∨ x = -1 := by
      have h13 : x ^ 2 = 1 := h10
      have : x = 1 ∨ x = -1 := by
        rw [sq_eq_one_iff] at h13
        tauto
      tauto

    cases h12 with
    | inl h14 =>
      exfalso
      apply hx1
      linarith
    | inr h15 =>
      exfalso
      apply hx2
      linarith

  field_simp [(show 1 - x ≠ 0 by assumption), (show 1 + x ≠ 0 by assumption), 
    (show 1 + x^2 ≠ 0 by assumption), (show 1 + x^4 ≠ 0 by assumption), 
    (show 1 + x^8 ≠ 0 by assumption), (show 1 - x ^ 16 ≠ 0 by assumption)]
  <;> nlinarith [sq_pos_of_ne_zero (show x - 1 ≠ 0 by intro h; apply hx1; linarith), 
          sq_pos_of_ne_zero (show x + 1 ≠ 0 by intro h; apply hx2; linarith), 
          sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg (x - 1), 
          sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 2 - x), sq_nonneg (x ^ 2 + x)]