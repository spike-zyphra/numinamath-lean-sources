import Mathlib

theorem algebra_12937 :
  IsLeast {n : ℕ | ∃ x y, n = x + y ∧ x > 0 ∧ y > 0 ∧ (1 / (x + 2000) : ℚ) + (1 / (y + 1999) : ℚ) = 1 / 2019} 4077 := by
  constructor
  · -- Show that 4077 belongs to the set
    use 2038, 2039
    all_goals norm_num
  · -- Show that any value in the set is ≥ 4077
    rintro n ⟨x, y, hn, hx, hy, heq⟩
    have h1 : (x : ℚ) > 0 := by exact_mod_cast hx
    have h2 : (y : ℚ) > 0 := by exact_mod_cast hy
    have eq2 : (x : ℚ) * (y : ℚ) + 1999 * (x : ℚ) + 2000 * (y : ℚ) + 2000 * 1999 = 2019 * ((x : ℚ) + (y : ℚ) + 3999) := by
      field_simp at heq
      nlinarith
    have h3 : (x : ℚ) + (y : ℚ) ≥ 4077 := by
      nlinarith [sq_nonneg ((x : ℚ) - 2038), sq_nonneg ((y : ℚ) - 2039), sq_nonneg ((x : ℚ) - (y : ℚ))]
    have h4 : x + y ≥ 4077 := by
      have h5 : (x : ℚ) + (y : ℚ) ≥ 4077 := by linarith
      exact_mod_cast h5
    linarith [h4, hn]