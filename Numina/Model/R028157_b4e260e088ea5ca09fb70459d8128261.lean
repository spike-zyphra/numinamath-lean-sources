import Mathlib

theorem algebra_214515 : {x : ℝ | ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ x = a / abs a + b / abs b + c / abs c + a * b * c / abs (a * b * c)} = {4, -4, 0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- First, prove that if x is in the left side, then x is in the right side.
    rintro ⟨a, b, c, ha, hb, hc, hx⟩
    have h1 : a / abs a = 1 ∨ a / abs a = -1 := by
      cases (le_or_lt 0 a) with
      | inl h =>
        have h2 : abs a = a := abs_of_nonneg h
        left
        field_simp [h2, show a ≠ 0 by assumption]
      | inr h =>
        have h2 : abs a = -a := abs_of_neg h
        right
        field_simp [h2, show a ≠ 0 by assumption]
    have h2 : b / abs b = 1 ∨ b / abs b = -1 := by
      cases (le_or_lt 0 b) with
      | inl h =>
        have h2 : abs b = b := abs_of_nonneg h
        left
        field_simp [h2, show b ≠ 0 by assumption]
      | inr h =>
        have h2 : abs b = -b := abs_of_neg h
        right
        field_simp [h2, show b ≠ 0 by assumption]
    have h3 : c / abs c = 1 ∨ c / abs c = -1 := by
      cases (le_or_lt 0 c) with
      | inl h =>
        have h2 : abs c = c := abs_of_nonneg h
        left
        field_simp [h2, show c ≠ 0 by assumption]
      | inr h =>
        have h2 : abs c = -c := abs_of_neg h
        right
        field_simp [h2, show c ≠ 0 by assumption]
    have h4 : a * b * c / abs (a * b * c) = (a / abs a) * (b / abs b) * (c / abs c) := by
      have h5 : abs (a * b * c) = abs a * abs b * abs c := by
        simp [abs_mul]
      rw [h5]
      field_simp [show abs a ≠ 0 by apply abs_ne_zero.mpr ha, show abs b ≠ 0 by apply abs_ne_zero.mpr hb, show abs c ≠ 0 by apply abs_ne_zero.mpr hc]
      <;> ring
    rw [h4] at hx
    rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> rcases h3 with (h3 | h3) <;> 
      norm_num [h1, h2, h3] at hx ⊢ <;> norm_num [hx] at *
    <;> tauto
  · -- Now the converse: if x is in the right side, then x is in the left side.
    rintro (rfl | rfl | rfl)
    · -- Case x = 4
      use 1, 1, 1
      norm_num [abs_of_pos]
    · -- Case x = -4
      use -1, -1, -1
      norm_num [abs_of_pos, abs_of_neg]
    · -- Case x = 0
      use -1, -1, 1
      norm_num [abs_of_pos, abs_of_neg]