import Mathlib

theorem algebra_301897 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ (10 / (x ^ 2 : ℚ) - 1 / y = 1 / 5)}.encard = 2 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ (10 / (x ^ 2 : ℚ) - 1 / y = 1 / 5)} = {(5, 5), (7, 245)} := by
    ext ⟨x, y⟩
    simp [-one_div, -pow_two]
    constructor
    · -- Assume (x, y) satisfies the equation with positive integers
      rintro ⟨hx, hy, heq⟩
      have h_eq1 : (10 : ℚ) / (x ^ 2 : ℚ) - (1 : ℚ) / (y : ℚ) = (1 : ℚ) / 5 := by
        exact_mod_cast heq
      have eq1 : (x : ℚ) > 0 := by exact_mod_cast hx
      have eq2 : (y : ℚ) > 0 := by exact_mod_cast hy
      have h_eq2 : 50 * (y : ℚ) = (x ^ 2 : ℚ) * ((y : ℚ) + 5) := by
        field_simp [pow_two, eq1, eq2] at h_eq1 ⊢
        linarith
      have h_eq4 : 50 * y = x ^ 2 * (y + 5) := by
        exact_mod_cast h_eq2
      have h2 : x ≤ 7 := by
        by_contra h
        push_neg at h
        have h4 : x ≥ 8 := by omega
        have h5 : x ^ 2 ≥ 64 := by nlinarith [show x ≥ 8 by omega]
        nlinarith [h_eq4, show y ≥ 1 by omega, show x ^ 2 ≥ 64 by nlinarith [show x ≥ 8 by omega]]
      interval_cases x <;> omega
    · -- Show that (5, 5) and (7, 245) satisfy the equation
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · constructor
        · norm_num
        · constructor
          · norm_num
          · norm_num
      · constructor
        · norm_num
        · constructor
          · norm_num
          · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_pair]
  all_goals norm_num