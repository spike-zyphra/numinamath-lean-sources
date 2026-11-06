import Mathlib

theorem algebra_251753 (x : ℝ) (hx : x^2 - 12 * x + 32 ≠ 0) :
    abs ((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) =
    -((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) ↔
    x ∈ Set.Ico 3 4 ∪ Set.Ico 7 8 := by
  constructor
  · -- Assume abs (A) = -A, prove the set membership.
    intro h_eq
    have h1 : ((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) ≤ 0 := by
      by_cases h3 : ((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) ≥ 0
      · -- in this case, abs y = y, so the equation becomes y = -y, so y = 0
        have h4 : abs ((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) =
            (x^2 - 10 * x + 21) / (x^2 - 12 * x + 32) := by
          rw [abs_of_nonneg h3]
        rw [h4] at h_eq
        linarith
      · -- in this case, abs y = -y, which is consistent with equation
        have h2 : abs ((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) =
            -((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) := by
          rw [abs_of_neg (by linarith)]
        rw [h2] at h_eq
        nlinarith [abs_nonneg ((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32))]
    by_cases h9 : x^2 - 12 * x + 32 > 0
    · -- denominator > 0
      have h10 : x^2 - 10 * x + 21 ≤ 0 := by
        have h11 : (x^2 - 10 * x + 21) / (x^2 - 12 * x + 32) ≤ (0 : ℝ) := h1
        apply (div_nonpos_iff).mp at h11
        cases h11 with
        | inl h12 =>
          nlinarith [h9]
        | inr h13 =>
          nlinarith [h9]
      have h17 : 3 ≤ x := by nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 7)]
      have h18 : x ≤ 7 := by nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 7)]
      by_cases h4 : x < (4 : ℝ)
      · -- x < 4
        left
        exact ⟨by linarith, by linarith⟩
      · -- x ≥ 4
        -- This interval is invalid as denominator >0, but for x in [4,7], numerator >0, so fraction >0 which contradicts h1.
        -- Therefore, x is excluded.
        have h5 : x < (4 : ℝ) := by nlinarith [sq_nonneg (x - 4), sq_nonneg (x - 8), h9]
        linarith
    · -- denominator ≤ 0
      have h9' : x^2 - 12 * x + 32 ≤ (0 : ℝ) := by
        by_contra h
        push_neg at h
        have : x^2 - 12 * x + 32 > (0 : ℝ) := by nlinarith
        linarith
      have h13 : x^2 - 12 * x + 32 < (0 : ℝ) := by
        by_contra h
        push_neg at h
        have h16 : x^2 - 12 * x + 32 = (0 : ℝ) := by
          linarith
        have h17 : x^2 - 12 * x + 32 = (0 : ℝ) := h16
        have h18 : x^2 - 12 * x + 32 = 0 := by nlinarith
        have h19 : x^2 - 12 * x + 32 ≠ 0 := hx
        contradiction
      have h14 : x^2 - 10 * x + 21 ≥ (0 : ℝ) := by
        have h15 : (x^2 - 10 * x + 21) / (x^2 - 12 * x + 32) ≤ (0 : ℝ) := by linarith [h1]
        have h16 : (x^2 - 10 * x + 21) ≥ (0 : ℝ) := by
          by_contra h
          push_neg at h
          have h17 : (x^2 - 10 * x + 21) / (x^2 - 12 * x + 32) > (0 : ℝ) := by
            apply div_pos_of_neg_of_neg
            linarith
            nlinarith
          nlinarith
        linarith
      have h17 : 7 ≤ x := by
        nlinarith [sq_nonneg (x - 7), sq_nonneg (x - 3), sq_nonneg (x - 4), sq_nonneg (x - 8)]
      have h18 : x < (8 : ℝ) := by
        nlinarith [h13, sq_nonneg (x - 4), sq_nonneg (x - 8)]
      right
      exact ⟨by linarith, by linarith⟩
  · -- Assume the set membership, prove abs (A) = -A
    intro h
    rcases h with (h | h)
    · -- x ∈ [3, 4)
      rcases h with ⟨hx3, hx4⟩
      have h21 : x^2 - 12 * x + 32 > 0 := by
        nlinarith [sq_nonneg (x - 4), sq_nonneg (x - 8)]
      have h22 : x^2 - 10 * x + 21 ≤ 0 := by
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 7)]
      have h1 : ((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) ≤ (0 : ℝ) := by
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Numerator ≤ 0
          linarith
        · -- Denominator > 0
          linarith
      have h24 : abs ((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) =
          -((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) := by
        rw [abs_of_nonpos (by linarith)]
      linarith [h24]
    · -- x ∈ [7, 8)
      rcases h with ⟨hx7, hx8⟩
      have h21 : x^2 - 12 * x + 32 < 0 := by
        nlinarith [sq_nonneg (x - 4), sq_nonneg (x - 8)]
      have h22 : x^2 - 10 * x + 21 ≥ 0 := by
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 7)]
      have h1 : ((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) ≤ (0 : ℝ) := by
        apply div_nonpos_of_nonneg_of_nonpos
        · -- Numerator ≥ 0
          linarith
        · -- Denominator < 0
          linarith
      have h24 : abs ((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) =
          -((x^2 - 10 * x + 21) / (x^2 - 12 * x + 32)) := by
        rw [abs_of_nonpos (by linarith)]
      linarith [h24]