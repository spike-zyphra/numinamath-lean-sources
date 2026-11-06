import Mathlib

open Real

theorem algebra_1303 (a b c : ℝ) (h : a * b * c ≠ 0) :
    4 ≥ a / abs a + b / abs b + c / abs c + a * b * c / abs (a * b * c) ∧
    a / abs a + b / abs b + c / abs c + a * b * c / abs (a * b * c) ≥ -4 := by

  have ha1 : a ≠ 0 := by
    by_contra h1
    have h2 : a * b * c = 0 := by
      rw [h1]
      norm_num
    contradiction

  have hb1 : b ≠ 0 := by
    by_contra h1
    have h2 : a * b * c = 0 := by
      rw [h1]
      norm_num
    contradiction

  have hc1 : c ≠ 0 := by
    by_contra h1
    have h2 : a * b * c = 0 := by
      rw [h1]
      norm_num
    contradiction

  have h1 : a / abs a = 1 ∨ a / abs a = -1 := by
    cases (le_or_lt 0 a) with
    | inl h2 =>
      -- a ≥ 0
      have h3 : abs a = a := abs_of_nonneg h2
      left
      field_simp [h3, ha1]
    | inr h2 =>
      -- a < 0
      have h3 : abs a = -a := abs_of_neg h2
      right
      field_simp [h3, ha1]

  have h2 : b / abs b = 1 ∨ b / abs b = -1 := by
    cases (le_or_lt 0 b) with
    | inl h3 =>
      -- b ≥ 0
      have h4 : abs b = b := abs_of_nonneg h3
      left
      field_simp [h4, hb1]
    | inr h3 =>
      -- b < 0
      have h4 : abs b = -b := abs_of_neg h3
      right
      field_simp [h4, hb1]

  have h3 : c / abs c = 1 ∨ c / abs c = -1 := by
    cases (le_or_lt 0 c) with
    | inl h4 =>
      -- c ≥ 0
      have h5 : abs c = c := abs_of_nonneg h4
      left
      field_simp [h5, hc1]
    | inr h4 =>
      -- c < 0
      have h5 : abs c = -c := abs_of_neg h4
      right
      field_simp [h5, hc1]

  have h4 : a * b * c / abs (a * b * c) = 1 ∨ a * b * c / abs (a * b * c) = -1 := by
    cases (le_or_lt 0 (a * b * c)) with
    | inl h5 =>
      -- a * b * c ≥ 0
      have h6 : abs (a * b * c) = a * b * c := abs_of_nonneg h5
      left
      field_simp [h6, h]
    | inr h5 =>
      -- a * b * c < 0
      have h6 : abs (a * b * c) = - (a * b * c) := abs_of_neg h5
      right
      field_simp [h6, h]

  constructor
  · -- Show that 4 is the maximum
    rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> rcases h3 with (h3 | h3) <;> rcases h4 with (h4 | h4)
    all_goals
      linarith

  · -- Show that -4 is the minimum
    rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> rcases h3 with (h3 | h3) <;> rcases h4 with (h4 | h4)
    all_goals
      linarith