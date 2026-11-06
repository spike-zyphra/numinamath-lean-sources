import Mathlib

theorem algebra_115299 (x : ℝ) (hx : x ≠ -2) (hx' : x ≠ -3) (hx'' : x ≠ -1) :
    1 + 3 / (x + 3) * (1 + 2 / (x + 2) * (1 + 1 / (x + 1))) = x ↔ x = 2 := by
  constructor
  · -- Assume left side, prove right side
    intro h
    have h1 : x + 1 ≠ 0 := by
      intro h2
      apply hx''
      linarith
    have h2 : x + 2 ≠ 0 := by
      intro h3
      apply hx
      linarith
    have h3 : x + 3 ≠ 0 := by
      intro h4
      apply hx'
      linarith
    have h4 : 1 + 3 / (x + 3) * (1 + 2 / (x + 2) * (1 + 1 / (x + 1))) = x := h
    have eq1 : 1 + 3 / (x + 3) * (1 + 2 / (x + 2) * (1 + 1 / (x + 1))) = (x + 4) / (x + 1) := by
      have eq2 : 1 + 1 / (x + 1) = (x + 2) / (x + 1) := by
        field_simp [h1]
        <;> ring
      have eq3 : 1 + 2 / (x + 2) * (1 + 1 / (x + 1)) = (x + 3) / (x + 1) := by
        rw [eq2]
        field_simp [h2, h1]
        <;> ring
      have eq4 : 1 + 3 / (x + 3) * (1 + 2 / (x + 2) * (1 + 1 / (x + 1))) = (x + 4) / (x + 1) := by
        rw [eq3]
        field_simp [h3, h1]
        <;> ring
      exact eq4
    rw [eq1] at h4
    have h5 : x + 4 = x * (x + 1) := by
      field_simp [h1] at h4
      linarith
    have h6 : x ^ 2 = 4 := by
      nlinarith
    have h7 : x = 2 ∨ x = -2 := by
      have h8 : x ^ 2 - 4 = 0 := by linarith
      have h9 : (x - 2) * (x + 2) = 0 := by nlinarith
      cases (mul_eq_zero.1 h9) with
      | inl h10 =>
        left
        linarith
      | inr h11 =>
        right
        linarith
    cases h7 with
    | inl h8 =>
      exact h8
    | inr h8 =>
      exfalso
      apply hx
      linarith
  · -- Assume right side, prove left side
    intro h
    rw [h]
    norm_num