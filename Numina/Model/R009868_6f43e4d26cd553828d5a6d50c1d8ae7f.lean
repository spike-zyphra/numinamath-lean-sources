import Mathlib

theorem algebra_251687 : {x : ℝ | x^2 - 5 * abs x + 6 = 0} = {-2, 2, -3, 3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward direction: if x^2 - 5 * |x| + 6 = 0, then x ∈ {-2, 2, -3, 3}
    intro h
    by_cases h1 : x ≥ 0
    · -- If x ≥ 0, then |x| = x
      rw [abs_of_nonneg h1] at h
      have h2 : x ^ 2 - 5 * x + 6 = 0 := by linarith
      have h3 : (x - 2) * (x - 3) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp h3) with h4 h5
      · -- x - 2 = 0, so x = 2
        have hx : x = 2 := by linarith
        simp [hx]
      · -- x - 3 = 0, so x = 3
        have hx : x = 3 := by linarith
        simp [hx]
    · -- Case x < 0, then |x| = -x
      rw [abs_of_neg (lt_of_not_ge h1)] at h
      have h2 : x ^ 2 + 5 * x + 6 = 0 := by linarith
      have h3 : (x + 2) * (x + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h3) with h4 h5
      · -- x + 2 = 0, so x = -2
        have hx : x = -2 := by linarith
        simp [hx]
      · -- x + 3 = 0, so x = -3
        have hx : x = -3 := by linarith
        simp [hx]
  · -- Reverse direction: if x ∈ {-2, 2, -3, 3}, then x^2 - 5 * |x| + 6 = 0
    rintro (rfl | rfl | rfl | rfl)
    · -- x = -2
      norm_num [abs_of_nonneg, abs_of_neg]
    · -- x = 2
      norm_num [abs_of_nonneg, abs_of_neg]
    · -- x = -3
      norm_num [abs_of_nonneg, abs_of_neg]
    · -- x = 3
      norm_num [abs_of_nonneg, abs_of_neg]