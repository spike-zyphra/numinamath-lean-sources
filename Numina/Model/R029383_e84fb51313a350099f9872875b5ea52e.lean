import Mathlib
theorem algebra_3844 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a / abs a + b / abs b + c / abs c + a * b * c / abs (a * b * c) = 4 ∨
    a / abs a + b / abs b + c / abs c + a * b * c / abs (a * b * c) = 0 ∨
    a / abs a + b / abs b + c / abs c + a * b * c / abs (a * b * c) = -4 := by

  have h1 : a / abs a = 1 ∨ a / abs a = -1 := by
    cases (le_or_lt 0 a) with
    | inl h => 
      have h2 : abs a = a := abs_of_nonneg h
      left
      field_simp [h2, ha]
    | inr h => 
      have h2 : abs a = -a := abs_of_neg h
      right
      field_simp [h2, ha]

  have h2 : b / abs b = 1 ∨ b / abs b = -1 := by 
    cases (le_or_lt 0 b) with
    | inl h => 
      have h2 : abs b = b := abs_of_nonneg h
      left
      field_simp [h2, hb]
    | inr h => 
      have h2 : abs b = -b := abs_of_neg h
      right
      field_simp [h2, hb]

  have h3 : c / abs c = 1 ∨ c / abs c = -1 := by 
    cases (le_or_lt 0 c) with
    | inl h => 
      have h2 : abs c = c := abs_of_nonneg h
      left
      field_simp [h2, hc]
    | inr h => 
      have h2 : abs c = -c := abs_of_neg h
      right
      field_simp [h2, hc]

  have h4 : a * b * c / abs (a * b * c) = (a / abs a) * (b / abs b) * (c / abs c) := by
    field_simp [abs_mul, abs_mul, ha, hb, hc]
    <;> ring

  rw [h4]

  rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> rcases h3 with (h3 | h3) <;> 
    norm_num [h1, h2, h3] <;> tauto