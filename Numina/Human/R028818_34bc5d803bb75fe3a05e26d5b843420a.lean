import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_197517 : {x : ℝ | x ≥ 1 ∧ sqrt (x + 3 - 4 * sqrt (x - 1)) + sqrt (x + 8 - 6 * sqrt (x - 1)) = 1 } = Set.Icc 5 10 := by
  ext x; simp
  constructor
  · -- First implication: equation implies 5 ≤ x and x ≤ 10
    rintro ⟨hx, h⟩
    have h1 : sqrt (x - 1) ≥ 0 := by apply sqrt_nonneg
    have h2 : sqrt (x - 1) ^ 2 = x - 1 := by
      refine Real.sq_sqrt (by linarith)
    have h3 : sqrt (x + 3 - 4 * sqrt (x - 1)) ≥ 0 := by
      apply sqrt_nonneg
    have h4 : sqrt (x + 8 - 6 * sqrt (x - 1)) ≥ 0 := by
      apply sqrt_nonneg

    have h5 : sqrt (x + 3 - 4 * sqrt (x - 1)) = |sqrt (x - 1) - 2| := by
      have h5 : sqrt (x + 3 - 4 * sqrt (x - 1)) = sqrt ((sqrt (x - 1) - 2) ^ 2) := by
        have h1 : (sqrt (x - 1) - 2) ^ 2 = x - 1 - 4 * sqrt (x - 1) + 4 := by
          calc
            (sqrt (x - 1) - 2) ^ 2 = (sqrt (x - 1)) ^ 2 - 4 * sqrt (x - 1) + 4 := by ring
            _ = x - 1 - 4 * sqrt (x - 1) + 4 := by rw [h2]
        have h2 : x + 3 - 4 * sqrt (x - 1) = x - 1 - 4 * sqrt (x - 1) + 4 := by ring
        rw [h2, h1]
      rw [h5]
      rw [Real.sqrt_sq_eq_abs]

    have h6 : sqrt (x + 8 - 6 * sqrt (x - 1)) = |sqrt (x - 1) - 3| := by
      have h6 : sqrt (x + 8 - 6 * sqrt (x - 1)) = sqrt ((sqrt (x - 1) - 3) ^ 2) := by
        have h1 : (sqrt (x - 1) - 3) ^ 2 = x - 1 - 6 * sqrt (x - 1) + 9 := by
          calc
            (sqrt (x - 1) - 3) ^ 2 = (sqrt (x - 1)) ^ 2 - 6 * sqrt (x - 1) + 9 := by ring
            _ = x - 1 - 6 * sqrt (x - 1) + 9 := by rw [h2]
        have h2 : x + 8 - 6 * sqrt (x - 1) = x - 1 - 6 * sqrt (x - 1) + 9 := by ring
        rw [h2, h1]
      rw [h6]
      rw [Real.sqrt_sq_eq_abs]
      
    rw [h5, h6] at h

    by_cases h7 : sqrt (x - 1) ≥ 2
    · -- Case 1: sqrt(x - 1) ≥ 2
      by_cases h8 : sqrt (x - 1) ≥ 3
      · -- Subcase 1.1: sqrt(x - 1) ≥ 3
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
        have h9 : sqrt (x - 1) = 3 := by nlinarith [h, h3, h4]
        have h10 : x = 10 := by
          have ht1 : sqrt (x - 1) ^ 2 = 3 ^ 2 := by rw [h9]
          rw [h2] at ht1
          nlinarith
        exact ⟨by linarith, by linarith⟩
      · -- Subcase 1.2: 2 ≤ sqrt(x - 1) < 3
        rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)] at h
        have h11 : 2 ≤ sqrt (x - 1) := by linarith
        have h12 : sqrt (x - 1) < 3 := by
          by_contra h12
          push_neg at h12
          have : sqrt (x - 1) ≥ 3 := by linarith
          linarith
        have h13 : 5 ≤ x := by
          have ht1 : 2 ≤ sqrt (x - 1) := h11
          have ht2 : sqrt (x - 1) ^ 2 ≥ 2 ^ 2 := by nlinarith [ht1, h1]
          rw [h2] at ht2
          linarith
        have h14 : x < 10 := by
          have ht1 : sqrt (x - 1) < 3 := h12
          have ht2 : sqrt (x - 1) ^ 2 < 3 ^ 2 := by nlinarith [ht1, h1]
          rw [h2] at ht2
          linarith
        exact ⟨h13, by linarith [show x ≤ 10 from by nlinarith]⟩
    · -- Case 2: sqrt(x - 1) < 2
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h
      have h15 : sqrt (x - 1) = 2 := by nlinarith [h, h3, h4]
      have h16 : x = 5 := by
        have ht1 : sqrt (x - 1) ^ 2 = 2 ^ 2 := by rw [h15]
        rw [h2] at ht1
        nlinarith
      exact ⟨by linarith, by linarith⟩

  · -- Second implication: 5 ≤ x and x ≤ 10 implies equation
    rintro ⟨hx1, hx2⟩
    have h1 : sqrt (x - 1) ≥ 0 := by apply sqrt_nonneg
    have h2 : sqrt (x - 1) ^ 2 = x - 1 := by
      refine Real.sq_sqrt (by linarith)
    have h3 : sqrt (x + 3 - 4 * sqrt (x - 1)) = |sqrt (x - 1) - 2| := by
      have h3 : sqrt (x + 3 - 4 * sqrt (x - 1)) = sqrt ((sqrt (x - 1) - 2) ^ 2) := by
        have h1 : (sqrt (x - 1) - 2) ^ 2 = x - 1 - 4 * sqrt (x - 1) + 4 := by
          calc
            (sqrt (x - 1) - 2) ^ 2 = (sqrt (x - 1)) ^ 2 - 4 * sqrt (x - 1) + 4 := by ring
            _ = x - 1 - 4 * sqrt (x - 1) + 4 := by rw [h2]
        have h2 : x + 3 - 4 * sqrt (x - 1) = x - 1 - 4 * sqrt (x - 1) + 4 := by ring
        rw [h2, h1]
      rw [h3]
      rw [Real.sqrt_sq_eq_abs]

    have h4 : sqrt (x + 8 - 6 * sqrt (x - 1)) = |sqrt (x - 1) - 3| := by
      have h4 : sqrt (x + 8 - 6 * sqrt (x - 1)) = sqrt ((sqrt (x - 1) - 3) ^ 2) := by
        have h1 : (sqrt (x - 1) - 3) ^ 2 = x - 1 - 6 * sqrt (x - 1) + 9 := by
          calc
            (sqrt (x - 1) - 3) ^ 2 = (sqrt (x - 1)) ^ 2 - 6 * sqrt (x - 1) + 9 := by ring
            _ = x - 1 - 6 * sqrt (x - 1) + 9 := by rw [h2]
        have h2 : x + 8 - 6 * sqrt (x - 1) = x - 1 - 6 * sqrt (x - 1) + 9 := by ring
        rw [h2, h1]
      rw [h4]
      rw [Real.sqrt_sq_eq_abs]

    have h5 : 2 ≤ sqrt (x - 1) := by
      have h5 : 5 ≤ x := hx1
      have h6 : x - 1 ≥ 4 := by linarith
      have h7 : sqrt (x - 1) ≥ sqrt 4 := Real.sqrt_le_sqrt (by linarith)
      have h8 : sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith

    have h6 : sqrt (x - 1) ≤ 3 := by
      have h6 : x ≤ 10 := hx2
      have h7 : x - 1 ≤ 9 := by linarith
      have h8 : sqrt (x - 1) ≤ sqrt 9 := Real.sqrt_le_sqrt (by linarith)
      have h9 : sqrt 9 = 3 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith

    rw [h3, h4]
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    constructor <;> linarith
