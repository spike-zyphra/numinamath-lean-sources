import Mathlib

theorem algebra_3776 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ((a / abs a) ^ 20) + ((b / abs b) ^ 18) + ((c / abs c) ^ 106) = 3 := by
  have h1 : (a / abs a) ^ 20 = 1 := by
    have h1a : a / abs a = 1 ∨ a / abs a = -1 := by 
      cases (le_or_lt 0 a) with
      | inl h_nonneg =>
        left
        have h_abs : abs a = a := abs_of_nonneg h_nonneg
        field_simp [h_abs, ha]
      | inr h_neg =>
        right
        have h_abs : abs a = -a := abs_of_neg h_neg
        field_simp [h_abs, ha]
    rcases h1a with (h | h)
    · rw [h]
      norm_num
    · rw [h]
      norm_num

  have h2 : (b / abs b) ^ 18 = 1 := by
    have h2a : b / abs b = 1 ∨ b / abs b = -1 := by 
      cases (le_or_lt 0 b) with
      | inl h_nonneg =>
        left
        have h_abs : abs b = b := abs_of_nonneg h_nonneg
        field_simp [h_abs, hb]
      | inr h_neg =>
        right
        have h_abs : abs b = -b := abs_of_neg h_neg
        field_simp [h_abs, hb]
    rcases h2a with (h | h)
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  
  have h3 : (c / abs c) ^ 106 = 1 := by
    have h3a : c / abs c = 1 ∨ c / abs c = -1 := by 
      cases (le_or_lt 0 c) with
      | inl h_nonneg =>
        left
        have h_abs : abs c = c := abs_of_nonneg h_nonneg
        field_simp [h_abs, hc]
      | inr h_neg =>
        right
        have h_abs : abs c = -c := abs_of_neg h_neg
        field_simp [h_abs, hc]
    rcases h3a with (h | h)
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  
  rw [h1, h2, h3]
  norm_num