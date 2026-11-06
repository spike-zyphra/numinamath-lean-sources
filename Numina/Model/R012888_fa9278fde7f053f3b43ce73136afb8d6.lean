import Mathlib

open Set Real

theorem algebra_323167 {M N : Set ℝ}
    (hM : M = {y | ∃ x ∈ Icc 1 4, y = x ^ ((1 : ℝ) / 2)}) (hN : N = {x | 0 < 1 - x}) :
    M ∩ (Set.univ \ N) = {x | 1 ≤ x ∧ x ≤ 2} := by
  ext x
  simp [hM, hN]
  constructor
  · -- Assume x ∈ M ∩ (Set.univ \ N)
    rintro ⟨⟨x0, hx0, h1⟩, h2⟩
    have hx01 : 1 ≤ x0 := by
      have h1 : x0 ∈ Icc (1 : ℝ) 4 := by
        simpa using hx0
      exact h1.1
    have hx02 : x0 ≤ 4 := by
      have h1 : x0 ∈ Icc (1 : ℝ) 4 := by
        simpa using hx0
      exact h1.2
    have h3 : 1 ≤ x := by
      have h4 : x = (x0 : ℝ) ^ ((1 : ℝ) / 2) := by
        linarith
      rw [h4]
      have h5 : (x0: ℝ) ≥ (1: ℝ) := by linarith
      have h6 : (x0: ℝ) ^ ((1: ℝ) / 2) ≥ (1: ℝ) := by
        have h1 : (1: ℝ) ≤ (x0: ℝ) := by linarith
        have h2 : (1: ℝ) ^ ((1: ℝ) / 2) ≤ (x0: ℝ) ^ ((1: ℝ) / 2) := by
          apply Real.rpow_le_rpow
          all_goals linarith
        have h3 : (1 : ℝ) ^ ((1 : ℝ) / 2) = (1 : ℝ) := by
          norm_num [Real.one_rpow]
        linarith [h3]
      linarith
    have h4 : x ≤ 2 := by
      have h4 : x = (x0 : ℝ) ^ ((1 : ℝ) / 2) := by
        linarith
      rw [h4]
      have h5 : (x0: ℝ) ≤ (4: ℝ) := by linarith
      have h6 : (x0: ℝ) ^ ((1: ℝ) / 2) ≤ (2: ℝ) := by
        have h7 : (x0: ℝ) ≤ (4: ℝ) := by linarith
        have h8 : (x0 : ℝ) ^ ((1: ℝ) / 2) ≤ ((4 : ℝ) : ℝ) ^ ((1 : ℝ) / 2) := by
          apply Real.rpow_le_rpow
          all_goals nlinarith
        have h9 : (4 : ℝ) ^ ((1 : ℝ) / 2) = (2 : ℝ) := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
        nlinarith [h9]
      linarith
    constructor <;> try linarith
  · -- Assume x ∈ {x | 1 ≤ x ∧ x ≤ 2}
    rintro ⟨hx1, hx2⟩
    constructor
    · -- Show x ∈ M
      use (x ^ 2)
      constructor
      · -- Show x² ∈ Icc 1 4
        constructor <;> try nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2)]
      · -- Show x = (x ^ 2) ^ (1 / 2)
        have h4 : (x ^ 2 : ℝ) ^ ((1 : ℝ) / 2) = x := by
          have h5 : ((x ^ 2 : ℝ) : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) := by
            have h9 : ((x ^ 2 : ℝ) : ℝ) ^ ((1 : ℝ) / 2) = (Real.sqrt (x ^ 2) : ℝ) := by
              rw [show ((x ^ 2 : ℝ) : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (x ^ 2) by
                rw [←Real.sqrt_eq_rpow]
              ]
              all_goals nlinarith
            rw [h9]
            have h8 : Real.sqrt (x ^ 2) = x := by
              rw [Real.sqrt_sq]
              all_goals linarith
            rw [h8]
            all_goals nlinarith
          linarith [h5]
        linarith [h4]
    · -- Show x ∉ N
      linarith