import Mathlib

open BigOperators Real Set


theorem inequalities_232470 {a : ℝ} (A B : Set ℝ)
  (hA : A = {x | abs (x - (a + 1)^2 / 2) ≤ ((a - 1)^2) / 2})
  (hB : B = {x | x^2 - 3 * (a + 1) * x + 2 * (3 * a + 1) ≤ 0}) :
  A ⊆ B ↔ a ∈ Icc 1 3 ∪ {-1} := by
  constructor
  · -- Forward implication: A ⊆ B → a ∈ [1,3] ∪ {-1}
    intro h
    have h1 : A = {x | 2 * a ≤ x ∧ x ≤ a ^ 2 + 1} := by
      ext x
      simp [hA]
      constructor
      · -- Assume abs (x - (a + 1)^2 / 2) ≤ (a - 1)^2 / 2, prove 2a ≤ x ∧ x ≤ a^2 + 1
        intro h
        have h2 : -(a - 1) ^ 2 / 2 ≤ x - (a + 1) ^ 2 / 2 ∧ x - (a + 1) ^ 2 / 2 ≤ (a - 1) ^ 2 / 2 := by
          constructor
          · linarith [abs_le.mp h]
          · linarith [abs_le.mp h]
        constructor
        · -- Prove 2a ≤ x
          nlinarith
        · -- Prove x ≤ a^2 + 1
          nlinarith
      · -- Assume 2a ≤ x ∧ x ≤ a^2 + 1, prove abs (x - (a + 1)^2 / 2) ≤ (a - 1)^2 / 2
        rintro ⟨h1, h2⟩
        have h2 : -(a - 1) ^ 2 / 2 ≤ x - (a + 1) ^ 2 / 2 ∧ x - (a + 1) ^ 2 / 2 ≤ (a - 1) ^ 2 / 2 := by
          constructor
          · -- Show -(a - 1) ^ 2 / 2 ≤ x - (a + 1) ^ 2 / 2
            nlinarith
          · -- Show x - (a + 1) ^ 2 / 2 ≤ (a - 1) ^ 2 / 2
            nlinarith
        apply abs_le.mpr
        constructor <;> linarith
    have h2 : B = {x | x ^ 2 - 3 * (a + 1) * x + 2 * (3 * a + 1) ≤ 0} := by
      exact hB
    have h3 : (2 * a : ℝ) ^ 2 - 3 * (a + 1) * (2 * a) + 2 * (3 * a + 1) ≤ 0 := by
      have h4 : (2 * a : ℝ) ∈ A := by
        rw [h1]
        constructor
        · -- Show 2a ≤ 2a
          linarith
        · -- Show 2a ≤ a^2 + 1
          nlinarith [sq_nonneg (a - 1)]
      have h5 : (2 * a : ℝ) ∈ B := h (h4)
      rw [h2] at h5
      simpa using h5
    have h4 : (a ^ 2 + 1 : ℝ) ^ 2 - 3 * (a + 1) * (a ^ 2 + 1) + 2 * (3 * a + 1) ≤ 0 := by
      have h5 : (a ^ 2 + 1 : ℝ) ∈ A := by
        rw [h1]
        constructor
        · -- Show 2a ≤ a^2 + 1
          nlinarith [sq_nonneg (a - 1)]
        · -- Show a^2 + 1 ≤ a^2 + 1
          linarith
      have h6 : (a ^ 2 + 1 : ℝ) ∈ B := h (h5)
      rw [h2] at h6
      simpa using h6
    by_cases h41 : a ≥ 1
    · -- Assume a ≥ 1
      have h7 : a ≤ 3 := by
        nlinarith [sq_nonneg (a - 3), sq_nonneg (a ^ 2 - 3 * a), sq_nonneg (a + 1), sq_nonneg (a - 1)]
      have h8 : a ∈ Icc 1 3 := by
        constructor <;> linarith
      simp [h8]
    · -- a < 1
      have h9 : a ≤ -1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
      have h10 : a = -1 := by
        nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1), sq_nonneg (a ^ 2 - 1)]
      simp [h10]
  · -- Backward implication: a ∈ [1,3] ∪ {-1} → A ⊆ B
    intro h
    have h1 : A = {x | 2 * a ≤ x ∧ x ≤ a ^ 2 + 1} := by
      ext x
      simp [hA]
      constructor
      · -- Assume abs (x - (a + 1)^2 / 2) ≤ (a - 1)^2 / 2, prove 2a ≤ x ∧ x ≤ a^2 + 1
        intro h
        have h2 : -(a - 1) ^ 2 / 2 ≤ x - (a + 1) ^ 2 / 2 ∧ x - (a + 1) ^ 2 / 2 ≤ (a - 1) ^ 2 / 2 := by
          constructor
          · linarith [abs_le.mp h]
          · linarith [abs_le.mp h]
        constructor
        · -- Prove 2a ≤ x
          nlinarith
        · -- Prove x ≤ a^2 + 1
          nlinarith
      · -- Assume 2a ≤ x ∧ x ≤ a^2 + 1, prove abs (x - (a + 1)^2 / 2) ≤ (a - 1)^2 / 2
        rintro ⟨h1, h2⟩
        have h2 : -(a - 1) ^ 2 / 2 ≤ x - (a + 1) ^ 2 / 2 ∧ x - (a + 1) ^ 2 / 2 ≤ (a - 1) ^ 2 / 2 := by
          constructor
          · -- Show -(a - 1) ^ 2 / 2 ≤ x - (a + 1) ^ 2 / 2
            nlinarith
          · -- Show x - (a + 1) ^ 2 / 2 ≤ (a - 1) ^ 2 / 2
            nlinarith
        apply abs_le.mpr
        constructor <;> linarith
    have h2 : B = {x | x ^ 2 - 3 * (a + 1) * x + 2 * (3 * a + 1) ≤ 0} := by
      exact hB
    rw [Set.subset_def]
    intro x hx
    rw [h1] at hx
    rw [h2]
    simp at hx ⊢
    rcases h with (h6 | h7)
    · -- a ∈ [1,3]
      rcases h6 with ⟨ha1, ha2⟩
      have h3 : 2 * a ≤ x := hx.1
      have h4 : x ≤ a ^ 2 + 1 := hx.2
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - (a ^ 2 + 1)), sq_nonneg (x - (3 * a + 1)), sq_nonneg (a - 1), sq_nonneg (a - 3), sq_nonneg (x - (a + 1) * 3 / 2)]
    · -- a = -1
      have ha3 : a = -1 := by
        simpa using h7
      rw [ha3]
      have h3 : -2 ≤ x := by
        nlinarith
      have h4 : x ≤ 2 := by
        nlinarith
      nlinarith [sq_nonneg (x ^ 2 - 4), sq_nonneg (x - 2), sq_nonneg (x + 2)]