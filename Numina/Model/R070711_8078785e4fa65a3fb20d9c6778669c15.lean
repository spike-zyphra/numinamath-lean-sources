import Mathlib

theorem algebra_321410 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (M : ℝ) (hM : M = a / abs a + b / abs b + c / abs c + a * b / abs (a * b) + b * c / abs (b * c) +
      c * a / abs (c * a) + a * b * c / abs (a * b * c)) :
    M = -1 ∨ M = 7 := by
  have h1 : a / abs a = 1 ∨ a / abs a = -1 := by
    cases (le_or_lt 0 a) with
    | inl h_nonneg =>
      -- a ≥ 0, so a / abs a = 1
      have h_abs : abs a = a := abs_of_nonneg h_nonneg
      left
      field_simp [h_abs, ha]
    | inr h_neg =>
      -- a < 0, so a / abs a = -1
      have h_abs : abs a = -a := abs_of_neg h_neg
      right
      field_simp [h_abs, ha]
  have h2 : b / abs b = 1 ∨ b / abs b = -1 := by
    cases (le_or_lt 0 b) with
    | inl h_nonneg =>
      -- b ≥ 0, so b / abs b = 1
      have h_abs : abs b = b := abs_of_nonneg h_nonneg
      left
      field_simp [h_abs, hb]
    | inr h_neg =>
      -- b < 0, so b / abs b = -1
      have h_abs : abs b = -b := abs_of_neg h_neg
      right
      field_simp [h_abs, hb]
  have h3 : c / abs c = 1 ∨ c / abs c = -1 := by
    cases (le_or_lt 0 c) with
    | inl h_nonneg =>
      -- c ≥ 0, so c / abs c = 1
      have h_abs : abs c = c := abs_of_nonneg h_nonneg
      left
      field_simp [h_abs, hc]
    | inr h_neg =>
      -- c < 0, so c / abs c = -1
      have h_abs : abs c = -c := abs_of_neg h_neg
      right
      field_simp [h_abs, hc]
  have h4 : a * b / abs (a * b) = (a / abs a) * (b / abs b) := by
    have h_abs_mul : abs (a * b) = abs a * abs b := by
      simp [abs_mul]
    rw [h_abs_mul]
    field_simp [ha, hb]
    <;> ring
  have h5 : b * c / abs (b * c) = (b / abs b) * (c / abs c) := by
    have h_abs_mul : abs (b * c) = abs b * abs c := by
      simp [abs_mul]
    rw [h_abs_mul]
    field_simp [hb, hc]
    <;> ring
  have h6 : c * a / abs (c * a) = (c / abs c) * (a / abs a) := by
    have h_abs_mul : abs (c * a) = abs c * abs a := by
      simp [abs_mul]
    rw [h_abs_mul]
    field_simp [hc, ha]
    <;> ring
  have h7 : a * b * c / abs (a * b * c) = (a / abs a) * (b / abs b) * (c / abs c) := by
    have h_abs_mul : abs (a * b * c) = abs a * abs b * abs c := by
      simp [abs_mul]
      <;> ring
    rw [h_abs_mul]
    field_simp [ha, hb, hc]
    <;> ring
  rw [hM]
  rw [h4, h5, h6, h7]
  rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> rcases h3 with (h3 | h3)
  <;> norm_num [h1, h2, h3]
  <;> tauto