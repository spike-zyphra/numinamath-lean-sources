import Mathlib

theorem algebra_11135 : ∃ S : Finset ℝ, S = { x : ℝ | x ≠ 0 ∧ abs (12 / x + 3) = 2 } ∧ S.prod id = 144 / 5 := by
  use { -12, -12 / 5 }
  constructor
  · -- Show the set equality
    ext x
    simp
    constructor
    · -- Assume x ∈ { -12, -12 / 5 }
      rintro (rfl | rfl)
      · constructor
        · norm_num
        · -- Show that abs (12 / (-12 : ℝ) + 3) = 2
          norm_num [abs_of_nonneg, abs_of_nonpos]
      · constructor
        · norm_num
        · -- Show that abs (12 / (-12 / 5 : ℝ) + 3) = 2
          norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Assume x satisfies the equation, prove it's in the set
      intro h
      rcases h with ⟨hx1, hx2⟩
      have h1 : abs (12 / x + 3) = 2 := hx2
      cases eq_or_eq_neg_of_abs_eq h1 with
      | inl h2 =>
        -- Case 1: 12/x + 3 = 2
        have h2' : 12 / x + 3 = 2 := by linarith
        have hx3 : x = -12 := by
          field_simp at h2' ⊢
          nlinarith
        simp [hx3]
      | inr h2 =>
        -- Case 2: 12/x + 3 = -2
        have h2' : 12 / x + 3 = -2 := by linarith
        have hx3 : x = -12 / 5 := by
          field_simp at h2' ⊢
          nlinarith
        simp [hx3]
  · -- Show the product is 144/5
    norm_num
    <;> norm_num