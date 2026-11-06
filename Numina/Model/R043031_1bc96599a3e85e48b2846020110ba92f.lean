import Mathlib


theorem algebra_11161
    (f : ℝ → ℝ)
    (hf : f = fun t => ((t - 2) ^ 2 * (t + 3)) / (2 * t - 3)) :
    {y | ∃ x, x ^ 2 + 4 * (x / (x - 2)) ^ 2 = 45 ∧ y = f x} = {2, 16} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume there exists x such that x^2 + 4(x/(x-2))^2 = 45 and y = f(x)
    rintro ⟨x, h_eq1, hy⟩
    have h_eq2 : y = ((x - 2) ^ 2 * (x + 3)) / (2 * x - 3) := by
      rw [hy, hf]
    have h_eq3 : x ^ 2 + 4 * (x / (x - 2)) ^ 2 = 45 := h_eq1
    have h1 : x - 2 ≠ 0 := by
      by_contra h
      have h2 : x = 2 := by linarith
      rw [h2] at h_eq3
      norm_num at h_eq3
    have h_eq4 : x ^ 2 * (x - 2) ^ 2 + 4 * x ^ 2 = 45 * (x - 2) ^ 2 := by
      have h_eq5 : x ^ 2 + 4 * (x / (x - 2)) ^ 2 = 45 := h_eq1
      field_simp [(show x - 2 ≠ 0 by assumption)] at h_eq5 ⊢
      nlinarith
    have h_eq5 : (x - 3) * (x - 6) * (x ^ 2 + 5 * x - 10) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show x - 2 ≠ 0 by assumption)]
    cases' (mul_eq_zero.mp h_eq5) with h_eq6 h_eq7
    cases' (mul_eq_zero.mp h_eq6) with h_eq8 h_eq9
    · -- Case x = 3
      have hx3 : x = 3 := by linarith
      rw [hx3] at h_eq2
      norm_num at h_eq2 ⊢
      tauto
    · -- Case x = 6
      have hx6 : x = 6 := by linarith
      rw [hx6] at h_eq2
      norm_num at h_eq2 ⊢
      tauto
    · -- Case x^2 + 5x - 10 = 0
      have h_eq10 : x ^ 2 + 5 * x - 10 = 0 := by
        nlinarith
      have h_eq11 : (2 * x - 3) ≠ 0 := by
        nlinarith [sq_pos_of_ne_zero (show x - 2 ≠ 0 by assumption), sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num)]
      have h_eq18 : ((x - 2) ^ 2 * (x + 3)) / (2 * x - 3) = 16 := by
        have h_eq18 : ((x - 2) ^ 2 * (x + 3)) = 16 * (2 * x - 3) := by
          nlinarith [sq_nonneg (x ^ 2 + 5 * x - 10), sq_pos_of_ne_zero (show x - 2 ≠ 0 by assumption), sq_pos_of_ne_zero (show 2 * x - 3 ≠ 0 by assumption), sq_nonneg (x ^ 2 - 16), sq_nonneg ((x - 3) * (x - 6)), sq_nonneg (x - 3), sq_nonneg (x - 6)]
        have h_eq15 : (2 * x - 3) ≠ 0 := h_eq11
        field_simp [h_eq15]
        linarith
      have h_eq23 : y = 16 := by
        rw [h_eq2]
        linarith [h_eq18]
      tauto
  · -- Assume y = 2 or 16
    rintro (rfl | rfl)
    · -- y = 2
      use 3
      constructor
      · norm_num
      · norm_num [hf]
    · -- y = 16
      use 6
      constructor
      · norm_num
      · norm_num [hf]