import Mathlib

open Real Set

theorem algebra_290827 (x y : ℝ) :
    max (max (x * y + 1) (x * y - x - y + 3)) (-2 * x * y + x + y + 2) ≥ 2 ∧
    (max (max (x * y + 1) (x * y - x - y + 3)) (-2 * x * y + x + y + 2) = 2 ↔
      (x = 1 ∧ y = 1)) := by
  constructor
  · -- First, prove that max (max (x * y + 1) (x * y - x - y + 3)) (-2 * x * y + x + y + 2) ≥ 2
    by_cases h1 : x * y + 1 ≥ x * y - x - y + 3
    · -- If x * y + 1 ≥ x * y - x - y + 3, then max (x * y + 1) (x * y - x - y + 3) = x * y + 1
      have h2 : max (x * y + 1) (x * y - x - y + 3) = x * y + 1 := by
        apply max_eq_left
        linarith
      rw [h2]
      by_cases h3 : x * y + 1 ≥ -2 * x * y + x + y + 2
      · -- Then max (x * y + 1) (-2 * x * y + x + y + 2) = x * y + 1
        have h4 : max (x * y + 1) (-2 * x * y + x + y + 2) = x * y + 1 := by
          apply max_eq_left
          linarith
        rw [h4]
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * y - 1)]
      · -- Otherwise max (x * y + 1) (-2 * x * y + x + y + 2) = -2 * x * y + x + y + 2
        have h4 : max (x * y + 1) (-2 * x * y + x + y + 2) = -2 * x * y + x + y + 2 := by
          apply max_eq_right
          linarith
        rw [h4]
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * y - 1)]
    · -- If not, max (x * y + 1) (x * y - x - y + 3) = x * y - x - y + 3
      have h2 : max (x * y + 1) (x * y - x - y + 3) = x * y - x - y + 3 := by
        apply max_eq_right
        linarith
      rw [h2]
      by_cases h3 : x * y - x - y + 3 ≥ -2 * x * y + x + y + 2
      · -- Then max (x * y - x - y + 3) (-2 * x * y + x + y + 2) = x * y - x - y + 3
        have h4 : max (x * y - x - y + 3) (-2 * x * y + x + y + 2) = x * y - x - y + 3 := by
          apply max_eq_left
          linarith
        rw [h4]
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * y - 1)]
      · -- Otherwise max (x * y - x - y + 3) (-2 * x * y + x + y + 2) = -2 * x * y + x + y + 2
        have h4 : max (x * y - x - y + 3) (-2 * x * y + x + y + 2) = -2 * x * y + x + y + 2 := by
          apply max_eq_right
          linarith
        rw [h4]
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * y - 1)]
  · -- Now, prove the equivalence for equality
    constructor
    · -- Forward direction: max (max (x * y + 1) (x * y - x - y + 3)) (-2 * x * y + x + y + 2) = 2 implies (x = 1 ∧ y = 1)
      intro h_eq
      by_cases h1 : x * y + 1 ≥ x * y - x - y + 3
      · -- If max (x * y + 1) (x * y - x - y + 3) = x * y + 1
        have h2 : max (x * y + 1) (x * y - x - y + 3) = x * y + 1 := by
          apply max_eq_left
          linarith
        rw [h2] at h_eq
        by_cases h3 : x * y + 1 ≥ -2 * x * y + x + y + 2
        · -- Then max (x * y + 1) (-2 * x * y + x + y + 2) = x * y + 1
          have h4 : max (x * y + 1) (-2 * x * y + x + y + 2) = x * y + 1 := by
            apply max_eq_left
            linarith
          rw [h4] at h_eq
          have h5 : x * y = 1 := by linarith
          have hn8 : (x - 1)^2 + (y - 1)^2 = 0 := by
            nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * (y - 1)), sq_nonneg ((x - 1) * (y - 1))]
          have hx1 : x = 1 := by
            nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
          have hy1 : y = 1 := by
            nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
          constructor
          · exact hx1
          · exact hy1
        · -- Then max (x * y + 1) (-2 * x * y + x + y + 2) = -2 * x * y + x + y + 2
          have h4 : max (x * y + 1) (-2 * x * y + x + y + 2) = -2 * x * y + x + y + 2 := by
            apply max_eq_right
            linarith
          rw [h4] at h_eq
          have hn8 : (x - 1)^2 + (y - 1)^2 = 0 := by
            nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * (y - 1)), sq_nonneg ((x - 1) * (y - 1))]
          have hx1 : x = 1 := by
            nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
          have hy1 : y = 1 := by
            nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
          constructor
          · exact hx1
          · exact hy1
      · -- If max (x * y + 1) (x * y - x - y + 3) = x * y - x - y + 3
        have h2 : max (x * y + 1) (x * y - x - y + 3) = x * y - x - y + 3 := by
          apply max_eq_right
          linarith
        rw [h2] at h_eq
        by_cases h3 : x * y - x - y + 3 ≥ -2 * x * y + x + y + 2
        · -- Then max (x * y - x - y + 3) (-2 * x * y + x + y + 2) = x * y - x - y + 3
          have h4 : max (x * y - x - y + 3) (-2 * x * y + x + y + 2) = x * y - x - y + 3 := by
            apply max_eq_left
            linarith
          rw [h4] at h_eq
          have hn8 : (x - 1)^2 + (y - 1)^2 = 0 := by
            nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * (y - 1)), sq_nonneg ((x - 1) * (y - 1))]
          have hx1 : x = 1 := by
            nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
          have hy1 : y = 1 := by
            nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
          constructor
          · exact hx1
          · exact hy1
        · -- Then max (x * y - x - y + 3) (-2 * x * y + x + y + 2) = -2 * x * y + x + y + 2
          have h4 : max (x * y - x - y + 3) (-2 * x * y + x + y + 2) = -2 * x * y + x + y + 2 := by
            apply max_eq_right
            linarith
          rw [h4] at h_eq
          have hn8 : (x - 1)^2 + (y - 1)^2 = 0 := by
            nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * (y - 1)), sq_nonneg ((x - 1) * (y - 1))]
          have hx1 : x = 1 := by
            nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
          have hy1 : y = 1 := by
            nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
          constructor
          · exact hx1
          · exact hy1
    · -- Backward direction: (x = 1 ∧ y = 1) implies max (max (x * y + 1) (x * y - x - y + 3)) (-2 * x * y + x + y + 2) = 2
      rintro ⟨hx, hy⟩
      norm_num [hx, hy]