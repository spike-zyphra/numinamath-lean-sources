import Mathlib

open Set Real

theorem inequalities_8367 (m : ℝ) (A B : Set ℝ)
    (hA : A = {x | (x - 1) / (2 * x - 1) ≤ 0})
    (hB : B = {x | x ^ 2 + 2 * x + m ≤ 0}) :
    A ⊆ B ↔ m ≤ -3 := by
  constructor
  · -- Assume A ⊆ B, prove m ≤ -3.
    intro h
    have h1 : (1 : ℝ) ∈ A := by
      rw [hA]
      norm_num
    have h2 : (1 : ℝ) ∈ B := h h1
    rw [hB] at h2
    have h3 : (1 : ℝ) ^ 2 + 2 * (1 : ℝ) + m ≤ 0 := by
      simpa using h2
    nlinarith
  · -- Assume m ≤ -3, prove A ⊆ B.
    intro hm
    intro x hx
    have h1 : x ∈ A := hx
    have h1' : (x - 1) / (2 * x - 1) ≤ 0 := by 
      rw [hA] at h1
      simpa using h1
    have h2 : x ≥ 1 / 2 := by
      by_contra h
      push_neg at h
      have h3 : 2 * x - 1 < 0 := by linarith
      have h4 : x - 1 < 0 := by linarith
      have h5 : (x - 1) / (2 * x - 1) ≥ 0 := by
        apply div_nonneg_of_nonpos
        all_goals linarith
      have h6 : (x - 1) / (2 * x - 1) = 0 := by linarith
      have h7 : 2 * x - 1 ≠ 0 := by
        nlinarith
      have h8 : x - 1 = 0 := by
        have h9 : (x - 1) / (2 * x - 1) = 0 := h6
        have h10 : x - 1 = 0 := by
          have h11 : (x - 1) / (2 * x - 1) = 0 := h9
          have h12 : 2 * x - 1 ≠ 0 := h7
          field_simp [h12] at h11 ⊢
          <;> linarith
        linarith
      have h9 : x = 1 := by linarith
      linarith
    -- Show that x ≤ 1
    have h3 : x ≤ 1 := by
      by_contra h
      push_neg at h
      have h4 : 2 * x - 1 > 0 := by linarith
      have h5 : x - 1 > 0 := by linarith
      have h6 : (x - 1) / (2 * x - 1) > 0 := by
        apply div_pos
        all_goals linarith
      linarith
    have h4 : x ^ 2 + 2 * x + m ≤ 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 1 / 2), sq_nonneg (x + 1), sq_nonneg (x), hm]
    rw [hB]
    simpa using h4