import Mathlib

theorem number_theory_249644 (x y : ℤ) (hx : x > 0) (hy : y > 0) :
    x^4 = y^2 + 71 ↔ (x = 6 ∧ y = 35) := by
  constructor
  · -- Assume x^4 = y^2 + 71, prove (x = 6 ∧ y = 35)
    intro h
    have h1 : x^4 - y^2 = 71 := by
      nlinarith
    have h2 : (x^2 - y) * (x^2 + y) = 71 := by
      nlinarith [h1]
    have h3 : (x^2 - y) ∣ 71 := by
      use (x^2 + y)
      linarith
    have h4 : (x^2 - y) = 1 ∨ (x^2 - y) = 71 := by
      have h5 : (x^2 - y) > 0 := by
        nlinarith [h1, sq_nonneg (x^2), sq_nonneg (y), h2]
      have h6 : (x^2 - y) ∣ 71 := h3
      have h7 : (x^2 - y) = 1 ∨ (x^2 - y) = 71 := by
        have h8 : (x^2 - y) ∣ 71 := h6
        have h9 : (x^2 - y) ≤ 71 := by
          exact Int.le_of_dvd (by omega) h8
        interval_cases h10 : (x^2 - y) <;> tauto
      assumption
    cases h4 with
    | inl h5 =>
      have h6 : x^2 + y = 71 := by
        nlinarith
      have h7 : x^2 = 36 := by
        nlinarith [h5, h6]
      have h8 : x = 6 := by
        nlinarith [h7, sq_nonneg (x ^ 2), sq_nonneg (x), hx]
      have h9 : y = 35 := by
        nlinarith [h7, h5]
      exact ⟨h8, h9⟩
    | inr h5 =>
      have h6 : x^2 + y = 1 := by
        nlinarith
      have h7 : x^2 + y > 1 := by
        nlinarith [sq_pos_of_pos hx, hy]
      linarith
  · -- Assume (x = 6 ∧ y = 35), prove x^4 = y^2 + 71
    rintro ⟨rfl, rfl⟩
    all_goals norm_num