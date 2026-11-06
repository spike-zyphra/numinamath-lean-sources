import Mathlib

theorem algebra_327001 (a : ℝ) (ha : -2 ≤ a) (B C : Set ℝ)
    (hB : B = {y | ∃ x, y = 2 * x + 3 ∧ -2 ≤ x ∧ x ≤ a})
    (hC : C = {z | ∃ x, z = x ^ 2 ∧ -2 ≤ x ∧ x ≤ a}) :
    C ⊆ B ↔ a ∈ Set.Icc (1 / 2) 3 := by
  constructor
  · -- Assume C ⊆ B
    intro h
    have h1 : 4 ∈ C := by
      rw [hC]
      use -2
      norm_num
      all_goals nlinarith
      all_goals nlinarith
    have h2 : 4 ∈ B := h h1
    have h3 : a ^ 2 ∈ C := by
      rw [hC]
      use a
      all_goals nlinarith
      all_goals nlinarith
    have h4 : a ^ 2 ∈ B := h h3
    constructor
    · -- Show 1/2 ≤ a
      have h5 : 4 ∈ B := h h1
      rw [hB] at h5
      rcases h5 with ⟨x, hx1, hx2, hx3⟩
      nlinarith
      all_goals nlinarith
    · -- Show a ≤ 3
      have h5 : a ^ 2 ∈ B := h4
      rw [hB] at h5
      rcases h5 with ⟨x, hx1, hx2, hx3⟩
      nlinarith [sq_nonneg (x - a), sq_nonneg (a - 3)]
      all_goals nlinarith
      all_goals nlinarith
  · -- Assume a ∈ [1 / 2, 3]
    rintro ⟨ha1, ha2⟩
    intro z hz
    rw [hC] at hz
    rcases hz with ⟨x, hz1, hx1, hx2⟩
    have h1 : z ∈ B := by
      rw [hB]
      use (x ^ 2 - 3) / 2
      constructor
      · -- Show that z = 2 * ((x ^ 2 - 3) / 2) + 3
        nlinarith
      constructor
      · -- Show that -2 ≤ (x ^ 2 - 3) / 2
        nlinarith [sq_nonneg (x - a), sq_nonneg (x + 2), sq_nonneg (a - 3), sq_nonneg (a - 1 / 2)]
      · -- Show that (x ^ 2 - 3) / 2 ≤ a
        nlinarith [sq_nonneg (x - a), sq_nonneg (x + 2), sq_nonneg (a - 3), sq_nonneg (a - 1 / 2)]
    simpa using h1