import Mathlib

theorem algebra_12816 :
    IsLeast {n | ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ (1 / x : ℚ) + 1 / (2 * y : ℚ) = 1 / 7 ∧ n = x * y} 98 := by
  constructor
  · -- Show 98 is in the set
    use 14, 7
    all_goals
      norm_num
  · -- Show no value less than 98 is in the set
    intro n hn
    rcases hn with ⟨x, y, hx1, hy1, heq, heq2⟩
    have heq2 : (1 / (x : ℚ) + 1 / (2 * (y : ℚ)) ) = (1 / 7 : ℚ) := by
      exact_mod_cast heq
    have hx2 : (x : ℚ) > 0 := by
      exact_mod_cast hx1
    have hy2 : (y : ℚ) > 0 := by
      exact_mod_cast hy1
    have eq1 : (x : ℚ) * (y : ℚ) * 2 = (x : ℚ) * 7 + (y : ℚ) * 14 := by
      have eq2 : (x : ℚ) > 0 := hx2
      have eq3 : (y : ℚ) > 0 := hy2
      have hx3 : (x : ℚ) ≠ 0 := by linarith
      have hy3 : (y : ℚ) ≠ 0 := by linarith
      field_simp at heq2 ⊢
      nlinarith
    have eq2 : (x : ℕ) * (y : ℕ) * 2 = (x : ℕ) * 7 + (y : ℕ) * 14 := by
      exact_mod_cast eq1
    by_contra h
    push_neg at h
    have h3 : x ≤ 48 := by
      nlinarith [eq2, show y ≥ 1 by linarith, h]
    have h4 : y ≤ 33 := by
      nlinarith [eq2, show x ≥ 1 by linarith, h]
    interval_cases x <;> omega