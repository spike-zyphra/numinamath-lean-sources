import Mathlib

theorem algebra_186782 (x : ℝ) (hx : x ≠ -2 ∧ x ≠ 2) :
    ((x^2 + 6) / (x^2 - 4))^2 = ((5 * x) / (4 - x^2))^2 ↔ x = -3 ∨ x = 3 := by
  constructor
  · -- Assume the equation holds, prove x = -3 or x = 3
    intro h
    have h1 : x ≠ -2 := hx.1
    have h2 : x ≠ 2 := hx.2
    have h3 : 4 - x^2 = -(x^2 - 4) := by ring
    have h4 : (5 * x) / (4 - x^2) = - (5 * x / (x^2 - 4)) := by
      rw [h3]
      rw [div_neg]
      <;> ring
    rw [h4] at h
    have h5 : ((x^2 + 6) / (x^2 - 4)) ^ 2 = ( (5 * x) / (x^2 - 4) ) ^ 2 := by
      nlinarith [h]
    have h6 : (x^2 + 6) / (x^2 - 4) = (5 * x) / (x^2 - 4) ∨ (x^2 + 6) / (x^2 - 4) = - (5 * x / (x^2 - 4)) := by
      have h7 : ((x^2 + 6) / (x^2 - 4)) ^ 2 - ((5 * x) / (x^2 - 4)) ^ 2 = 0 := by
        nlinarith [h5]
      have h8 : ((x^2 + 6) / (x^2 - 4) - (5 * x) / (x^2 - 4)) * ((x^2 + 6) / (x^2 - 4) + (5 * x) / (x^2 - 4)) = 0 := by
        ring_nf at h7 ⊢
        <;> nlinarith
      cases (mul_eq_zero.mp h8) with
      | inl h9 =>
        left
        linarith
      | inr h10 =>
        right
        linarith
    rcases h6 with h6 | h6
    · -- Case 1: $\frac{x^2 + 6}{x^2 - 4} = \frac{5x}{x^2 - 4}$
      have h7 : x^2 + 6 = 5 * x := by
        have h8 : x^2 - 4 ≠ 0 := by
          intro h9
          have : x = 2 ∨ x = -2 := by
            have h10 : x^2 = 4 := by linarith
            have h11 : x = 2 ∨ x = -2 := by
              apply eq_or_eq_neg_of_sq_eq_sq
              norm_num
              linarith
            assumption
          cases this with
          | inl h12 =>
            exfalso
            apply h2
            linarith
          | inr h13 =>
            exfalso
            apply h1
            linarith
        field_simp [h8] at h6
        nlinarith
      have h8 : (x - 2) * (x - 3) = 0 := by linarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · -- Case x = 2 is excluded
        exfalso
        apply h2
        linarith
      · -- So x = 3
        right
        linarith
    · -- Case 2: $\frac{x^2 + 6}{x^2 - 4} = -\frac{5x}{x^2 - 4}$
      have h7 : x^2 + 6 = -5 * x := by
        have h8 : x^2 - 4 ≠ 0 := by
          intro h9
          have : x = 2 ∨ x = -2 := by
            have h10 : x^2 = 4 := by linarith
            have h11 : x = 2 ∨ x = -2 := by
              apply eq_or_eq_neg_of_sq_eq_sq
              norm_num
              linarith
            assumption
          cases this with
          | inl h12 =>
            exfalso
            apply h2
            linarith
          | inr h13 =>
            exfalso
            apply h1
            linarith
        field_simp [h8] at h6
        nlinarith
      have h8 : (x + 2) * (x + 3) = 0 := by linarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · -- Case x = -2 is excluded
        exfalso
        apply h1
        linarith
      · -- So x = -3
        left
        linarith
  · -- Assume x = -3 or x = 3, prove the equation
    rintro (h | h)
    · -- Case x = -3
      rw [h]
      norm_num
    · -- Case x = 3
      rw [h]
      norm_num