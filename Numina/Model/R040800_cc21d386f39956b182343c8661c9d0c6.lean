import Mathlib

theorem algebra_10327 : IsGreatest {t : ℝ | t ≠ 8 ∧ t ≠ -5 ∧ (t ^ 2 - t - 56) / (t - 8) = 3 / (t + 5)} (-4) := by
  constructor
  · -- Show -4 is in the set.
    constructor
    · -- Show -4 ≠ 8.
      norm_num
    constructor
    · -- Show -4 ≠ -5.
      norm_num
    · -- Verify the equation for t = -4.
      norm_num 
  · -- Show -4 is greatest in the set.
    intro t ht
    rcases ht with ⟨htne8, htnem5, heq⟩
    have eq1 : (t ^ 2 - t - 56) / (t - 8) = t + 7 := by
      have ht1 : t - 8 ≠ 0 := by
        intro h
        apply htne8
        linarith 
      have ht2 : t ^ 2 - t - 56 = (t - 8) * (t + 7) := by
        ring 
      rw [ht2] 
      field_simp [ht1]
      <;> linarith 
    rw [eq1] at heq 
    have ht2 : t + 5 ≠ 0 := by 
      intro h
      apply htnem5 
      linarith 
    have ht3 : (t + 7) * (t + 5) = 3 := by
      have h1 : t + 5 ≠ 0 := ht2 
      field_simp [h1] at heq
      nlinarith 
    have ht4 : (t + 4) * (t + 8) = 0 := by
      nlinarith [ht3]
    cases' (mul_eq_zero.1 ht4) with h1 h2
    · -- Case where t + 4 = 0.
      linarith 
    · -- Case where t + 8 = 0.
      linarith