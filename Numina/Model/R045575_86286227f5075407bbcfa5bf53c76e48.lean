import Mathlib

open Set Real

theorem algebra_289637 {a : ℝ} (B : Set ℝ) (hB : B = {x | x^2 - a * x - 4 ≤ 0}) (A : Set ℝ)
    (hA : A = {x | -2 ≤ x ∧ x < 4}) : B ⊆ A ↔ 0 ≤ a ∧ a < 3 := by
  constructor
  · -- Assume B ⊆ A, prove 0 ≤ a ∧ a < 3
    intro h
    constructor
    · -- Prove 0 ≤ a
      by_contra ha
      push_neg at ha
      have h1 : a < 0 := ha
      have h3 : ∃ x, x ∈ B ∧ x < -2 := by
        have h4 : (a - Real.sqrt (a^2 + 16)) / 2 < -2 := by
          have h2' : a < 0 := h1
          nlinarith [Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show (a^2 + 16 : ℝ) ≥ 0 by nlinarith)]
        use (a - Real.sqrt (a^2 + 16)) / 2
        constructor
        · -- Show that $((a - Real.sqrt (a^2 + 16)) / 2) ∈ B$
          rw [hB]
          have h5 : ((a - Real.sqrt (a^2 + 16)) / 2) ^2 - a * ((a - Real.sqrt (a^2 + 16)) / 2) - 4 ≤ 0 := by
            nlinarith [Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show (a^2 + 16 : ℝ) ≥ 0 by nlinarith)]
          simpa using h5
        · -- Show that $(a - Real.sqrt (a^2 + 16)) / 2 < -2$
          linarith
      rcases h3 with ⟨x, hx1, hx2⟩
      have h4 : x ∈ A := h hx1
      rw [hA] at h4
      simp at h4
      linarith
    · -- Prove a < 3
      by_contra ha
      push_neg at ha
      have h5 : a ≥ 3 := by linarith
      have h6 : (4 : ℝ) ∈ B := by
        rw [hB]
        show (4 : ℝ) ^ 2 - a * (4 : ℝ) - 4 ≤ 0
        nlinarith
      have h7 : (4 : ℝ) ∈ A := h h6
      rw [hA] at h7
      simp at h7
      all_goals nlinarith
  · -- Assume 0 ≤ a ∧ a < 3, prove B ⊆ A
    rintro ⟨ha1, ha2⟩
    intro x hx
    have hx1 : x^2 - a * x - 4 ≤ 0 := by
      rw [hB] at hx
      simpa using hx
    have h2 : -2 ≤ x := by
      nlinarith [sq_nonneg (x - a / 2), sq_nonneg (x + 2), sq_nonneg (x - 4), ha1, sq_nonneg (a - 2), Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show (a^2 + 16 : ℝ) ≥ 0 by nlinarith)]
    have h3 : x < 4 := by
      nlinarith [sq_nonneg (x - a / 2), sq_nonneg (x - 4), sq_nonneg (x + 2), ha1, ha2, sq_nonneg (a - 2), Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show (a^2 + 16 : ℝ) ≥ 0 by nlinarith)]
    rw [hA]
    exact ⟨h2, h3⟩