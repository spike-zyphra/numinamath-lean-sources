import Mathlib

theorem algebra_1187 {a b c : ℝ} (h : a * b * c ≠ 0) (m : ℝ)
    (hm : m = (2 * a / abs a) * (3 * b / abs b) * (4 * c / abs c)) :
    m^2 + 2 * m + 1 = 625 ∨ m^2 + 2 * m + 1 = 529 := by

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
  
  have h4 : a / abs a = 1 ∨ a / abs a = -1 := by
    cases (le_or_lt 0 a) with
    | inl h5 =>
      -- case a ≥ 0
      have h6 : abs a = a := abs_of_nonneg h5
      left 
      field_simp [h6, show a ≠ 0 by exact ha1]
    | inr h6 =>
      -- case a < 0
      have h7 : abs a = -a := abs_of_neg h6
      right
      field_simp [h7, show a ≠ 0 by exact ha1]

  have h5 : b / abs b = 1 ∨ b / abs b = -1 := by 
    cases (le_or_lt 0 b) with 
    | inl h5 =>
      -- case b ≥ 0
      have h6 : abs b = b := abs_of_nonneg h5
      left 
      field_simp [h6, show b ≠ 0 by exact hb1]
    | inr h6 =>
      -- case b < 0
      have h7 : abs b = -b := abs_of_neg h6
      right
      field_simp [h7, show b ≠ 0 by exact hb1]

  have h6 : c / abs c = 1 ∨ c / abs c = -1 := by 
    cases (le_or_lt 0 c) with 
    | inl h5 =>
      -- case c ≥ 0
      have h6 : abs c = c := abs_of_nonneg h5
      left 
      field_simp [h6, show c ≠ 0 by exact hc1]
    | inr h6 =>
      -- case c < 0
      have h7 : abs c = -c := abs_of_neg h6
      right
      field_simp [h7, show c ≠ 0 by exact hc1]

  rcases h4 with (h4 | h4) <;> rcases h5 with (h5 | h5) <;> rcases h6 with (h6 | h6)
  all_goals
    have hm1 : m = 24 * ( (a / abs a) * (b / abs b) * (c / abs c) ) := by 
      rw [hm]
      have h7 : (2 * a / abs a) = 2 * (a / abs a) := by ring
      have h8 : (3 * b / abs b) = 3 * (b / abs b) := by ring
      have h9 : (4 * c / abs c) = 4 * (c / abs c) := by ring
      rw [h7, h8, h9]
      <;> ring
    rw [hm1]
    have h8 : (a / abs a) * (b / abs b) * (c / abs c) = 1 ∨ (a / abs a) * (b / abs b) * (c / abs c) = -1 := by
      rw [h4, h5, h6]
      norm_num
    rcases h8 with (h8 | h8)
    · -- case m = 24
      rw [h8]
      norm_num
    · -- case m = -24
      rw [h8]
      norm_num