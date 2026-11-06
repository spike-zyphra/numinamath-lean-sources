import Mathlib

theorem algebra_2535 {a : ℝ} (ha : a ≠ 0) :
    a / abs a + (a ^ 2) / abs (a ^ 2) + (a ^ 3) / abs (a ^ 3) = 3 ∨ a / abs a + (a ^ 2) / abs (a ^ 2) + (a ^ 3) / abs (a ^ 3) = -1 := by
  have h1 : abs (a ^ 2) = a ^ 2 := by
    rw [abs_of_nonneg]
    have : a ^ 2 ≥ 0 := sq_nonneg a
    tauto
  have h2 : abs (a ^ 3) = abs a ^ 3 := by
    simp [abs_pow]
  have h3 : (a ^ 2) / abs (a ^ 2) = 1 := by
    rw [h1]
    field_simp [ha]
  have h4 : (a ^ 3) / abs (a ^ 3) = (a / abs a) ^ 3 := by
    rw [h2]
    field_simp [ha, pow_succ]
    <;> ring
  have h5 : a / abs a = 1 ∨ a / abs a = -1 := by
    cases (le_or_lt 0 a) with
    | inl h =>
      -- a ≥ 0, so a / abs a = 1
      have ha1 : abs a = a := abs_of_nonneg h
      left
      field_simp [ha1, ha]
    | inr h =>
      -- a < 0, so a / abs a = -1
      have ha2 : abs a = -a := abs_of_neg h
      right
      field_simp [ha2, ha]
  rcases h5 with (h5 | h5)
  · -- a / abs a = 1
    have h6 : a / abs a + (a ^ 2) / abs (a ^ 2) + (a ^ 3) / abs (a ^ 3) = 3 := by
      rw [h3, h4, h5]
      norm_num
    left
    exact h6
  · -- a / abs a = -1
    have h7 : a / abs a + (a ^ 2) / abs (a ^ 2) + (a ^ 3) / abs (a ^ 3) = -1 := by
      rw [h3, h4, h5]
      norm_num
    right
    exact h7