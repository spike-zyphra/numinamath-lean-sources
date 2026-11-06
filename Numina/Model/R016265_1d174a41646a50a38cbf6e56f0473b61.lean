import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_244427 : range (λ x => abs (cos x) - cos (2 * x)) = {y | 0 ≤ y ∧ y ≤ 9 / 8} := by
  ext y
  simp only [mem_range, mem_setOf_eq, mem_setOf_eq]
  constructor
  · -- Assume y is in the range
    rintro ⟨x, hx⟩
    have h1 : -1 ≤ cos x ∧ cos x ≤ 1 := by apply cos_mem_Icc
    have h2 : 0 ≤ abs (cos x) := by apply abs_nonneg
    have h3 : cos (2 * x) = 2 * (cos x) ^ 2 - 1 := by
      rw [cos_two_mul]
    rw [h3] at hx
    set c := (cos x : ℝ) with hc
    have hc1 : -1 ≤ c ∧ c ≤ 1 := by
      have hcos := cos_mem_Icc x
      simp [hc] at hcos ⊢
      tauto
    have hy2 : y = abs c - 2 * c ^ 2 + 1 := by
      linarith
    by_cases h : c ≥ 0
    · -- If c ≥ 0, then abs c = c
      have h5 : abs c = c := abs_of_nonneg h
      rw [h5] at hy2
      constructor
      · -- Show 0 ≤ y
        nlinarith [sq_nonneg (c - 0), h]
      · -- Show y ≤ 9 / 8
        nlinarith [sq_nonneg (c - 1 / 4), h, sq_nonneg (c), sq_nonneg (c - 1)]
    · -- If c < 0, then abs c = -c
      have h8 : abs c = -c := abs_of_neg (lt_of_not_ge h)
      rw [h8] at hy2
      constructor
      · -- Show 0 ≤ y
        nlinarith [sq_nonneg (c + 0), h]
      · -- Show y ≤ 9 / 8
        nlinarith [sq_nonneg (c + 1 / 4), h, sq_nonneg (c + 1), sq_nonneg (c)]
  · -- Assume y in { y | 0 ≤ y ∧ y ≤ 9 / 8 }
    rintro ⟨hy1, hy2⟩
    by_cases h1 : y ≤ 1
    · -- If y ≤ 1, solve using c in [0, 1]
      have hc2 : ∃ c : ℝ, c ≥ 0 ∧ c ≤ 1 ∧ y + 2 * c ^ 2 - c - 1 = 0 := by
        use (1 + Real.sqrt (1 + 8 * (1 - y))) / 4
        constructor
        · -- Show c ≥ 0
          nlinarith [Real.sqrt_nonneg (1 + 8 * (1 - y)), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 8 * (1 - y) by linarith)]
        constructor
        · -- Show c ≤ 1
          nlinarith [Real.sqrt_nonneg (1 + 8 * (1 - y)), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 8 * (1 - y) by linarith)]
        · -- Show quadratic equation holds
          nlinarith [Real.sqrt_nonneg (1 + 8 * (1 - y)), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 8 * (1 - y) by linarith)]
      rcases hc2 with ⟨c, hc1, hc2, heq⟩
      use Real.arccos c
      have heq6 : cos (Real.arccos c) = c := by
        apply Real.cos_arccos
        all_goals linarith
      have heq7 : cos (2 * (Real.arccos c)) = 2 * c ^ 2 - 1 := by
        rw [show 2 * (Real.arccos c) = 2 * (Real.arccos c) by ring]
        rw [cos_two_mul]
        simp [show cos (Real.arccos c) = c by linarith [Real.cos_arccos (show -1 ≤ c by linarith) (show c ≤ 1 by linarith) ] ]
        all_goals linarith
      rw [heq7, heq6]
      have h5 : abs (c : ℝ) = c := abs_of_nonneg hc1
      nlinarith [h5, heq, sq_nonneg (c - 1 / 4)]
    · -- If y > 1, solve using c in [-1, 0]
      have hc2 : ∃ c : ℝ, c ≤ 0 ∧ -1 ≤ c ∧ y + 2 * c ^ 2 + c - 1 = 0 := by
        use (-1 + Real.sqrt (1 + 8 * (1 - y))) / 4
        constructor
        · -- Show c ≤ 0
          nlinarith [Real.sqrt_nonneg (1 + 8 * (1 - y)), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 8 * (1 - y) by linarith)]
        constructor
        · -- Show -1 ≤ c
          nlinarith [Real.sqrt_nonneg (1 + 8 * (1 - y)), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 8 * (1 - y) by linarith)]
        · -- Show quadratic equation holds
          nlinarith [Real.sqrt_nonneg (1 + 8 * (1 - y)), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 8 * (1 - y) by linarith)]
      rcases hc2 with ⟨c, hc1, hc2, heq⟩
      use Real.arccos (-c)
      have heq6 : cos (Real.arccos (-c)) = -c := by
        apply Real.cos_arccos
        all_goals nlinarith  -- Simplify goals using facts about c
      have heq7 : cos (2 * (Real.arccos (-c))) = 2 * (-c) ^ 2 - 1 := by
        rw [show 2 * (Real.arccos (-c)) = 2 * (Real.arccos (-c)) by ring]
        rw [cos_two_mul]
        simp [show cos (Real.arccos (-c)) = -c by linarith [Real.cos_arccos (show -1 ≤ -c by nlinarith) (show -c ≤ 1 by nlinarith) ] ]
        all_goals nlinarith  -- Simplify goals using facts about c
      rw [heq7, heq6]
      have h5 : abs (-c : ℝ) = abs c := by
        rw [abs_neg]
      have h5' : abs (-c : ℝ) = abs c := h5
      -- Use cases for c to complete the proof
      by_cases hc_nonneg : c ≥ 0
      · -- If c ≥ 0, then abs c = c
        have h5abs : abs c = c := abs_of_nonneg hc_nonneg
        rw [h5'] at *
        -- Now we know abs (-c) = c
        -- Substitute into the goal to finish
        nlinarith [h5abs, heq, sq_nonneg (c + 1 / 4)]
      · -- If c < 0, then abs c = -c
        have h5abs : abs c = -c := abs_of_neg (lt_of_not_ge hc_nonneg)
        rw [h5'] at *
        -- Now we know abs (-c) = -c
        -- Substitute into the goal to finish
        nlinarith [h5abs, heq, sq_nonneg (c + 1 / 4)]