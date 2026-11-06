import Mathlib

open Real

theorem algebra_608561:
  (∀ a b c : ℝ, a + b + c = 5 ∧ (1 ≤ a ∧ a ≤ 2) ∧ (1 ≤ b ∧ b ≤ 2) ∧ (1 ≤ c ∧ c ≤ 2) → (1/(a+b)+1/(b+c) ≥ 4/7))
  ∧ (∃ a b c : ℝ, a+b+c = 5 ∧ (1 ≤ a ∧ a ≤ 2) ∧ (1 ≤ b ∧ b ≤ 2)  ∧ (1 ≤ c ∧ c ≤ 2) ∧ 1/(a+b)+1/(b+c) = 4/7) := by
  constructor
  · -- First part: proving the inequality.
    intro a b c h
    rcases h with ⟨h1, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩⟩
    have h2 : 0 < a + b := by
      nlinarith
    have h3 : 0 < b + c := by
      nlinarith
    have h4 : 0 < (a + b) * (b + c) := by
      positivity
    have h5 : 1 / (a + b) + 1 / (b + c) - 4 / 7 ≥ 0 := by
      have pos1 : 0 < (a + b) := by
        nlinarith
      have pos2 : 0 < (b + c) := by
        nlinarith
      have pos3 : 0 < (a + b) * (b + c) := by
        positivity
      have h6 : 1 / (a + b) + 1 / (b + c) - 4 / 7 = ( (b + c + (a + b) ) - 4 / 7 * ( (a + b) * (b + c) ) ) / ( (a + b) * (b + c) ) := by
        field_simp
        ring
      rw [h6]
      have pos4 : 0 < (a + b) * (b + c) := by
        positivity
      have h7 : ( (b + c + (a + b) ) - 4 / 7 * ( (a + b) * (b + c) ) ) ≥ 0 := by
        nlinarith [sq_nonneg (a + b - 3.5), sq_nonneg (b + c - 3.5), sq_nonneg (b - 2), sq_nonneg (a - 1.5), sq_nonneg (c - 1.5), mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1), mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1), mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1) ]
      have h8 : ( (b + c + (a + b) ) - 4 / 7 * ( (a + b) * (b + c) ) ) / ( (a + b) * (b + c) ) ≥ 0 := by
        apply div_nonneg
        linarith
        all_goals positivity
      linarith
    linarith
  · -- Second part: showing existence with equality.
    use 1.5, 2, 1.5
    constructor
    · -- Check a + b + c = 5
      norm_num
    constructor
    · -- Check 1 ≤ a ∧ a ≤ 2
      norm_num
    constructor
    · -- Check 1 ≤ b ∧ b ≤ 2
      norm_num
    constructor
    · -- Check 1 ≤ c ∧ c ≤ 2
      norm_num
    · -- Check equality holds
      norm_num