import Mathlib

open Set Real

theorem algebra_197016 {a : ℝ} (A B : Set ℝ)
    (hA : A = Ico (-2) 4) (hB : B = {x | x^2 - a * x - 4 ≤ 0}) :
    B ⊆ A ↔ 0 ≤ a ∧ a < 3 := by
  constructor
  · -- Assume B ⊆ A, prove 0 ≤ a ∧ a < 3
    intro h
    have h1 : B ⊆ A := h
    -- Show 0 ≤ a
    have h16 : 0 ≤ a := by
      by_contra h5
      push_neg at h5
      -- Let's pick the left most point of B.
      have h20 : (a - Real.sqrt (a^2 + 16)) / 2 ∈ B := by
        rw [hB]
        have h21 : ((a - Real.sqrt (a^2 + 16)) / 2) ^ 2 - a * ((a - Real.sqrt (a^2 + 16)) / 2) - 4 ≤ 0 := by
          nlinarith [Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show 0 ≤ (a^2 + 16 : ℝ) by nlinarith)]
        simpa using h21
      have h22 : (a - Real.sqrt (a^2 + 16)) / 2 ∈ A := by
        apply h1
        exact h20
      rw [hA] at h22
      have h23 : -2 ≤ (a - Real.sqrt (a^2 + 16)) / 2 := by
        simp at h22 ⊢
        linarith
      nlinarith [Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show 0 ≤ (a^2 + 16 : ℝ) by nlinarith)]
    -- Show a < 3
    have h12 : a < 3 := by
      have h13 : (4 : ℝ) ∉ B := by
        intro h4
        have h4' : (4 : ℝ) ∈ B := h4
        have h4inA : (4 : ℝ) ∈ A := h (h4')
        rw [hA] at h4inA
        simp at h4inA
      rw [hB] at h13
      simp at h13
      nlinarith
    -- Combine the results
    exact ⟨h16, h12⟩
  · -- Assume 0 ≤ a ∧ a < 3, prove B ⊆ A
    rintro ⟨ha1, ha2⟩
    intro x hx
    have hx1 : x^2 - a * x - 4 ≤ 0 := by
      rw [hB] at hx
      simpa using hx
    have h2 : -2 ≤ x := by
      nlinarith [sq_nonneg (x - (-2)), sq_nonneg (x - 4), Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show 0 ≤ (a^2 + 16 : ℝ) by nlinarith)]
    have h3 : x < (4 : ℝ) := by
      nlinarith [sq_nonneg (x - 4), sq_nonneg (x - (-2)), Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show 0 ≤ (a^2 + 16 : ℝ) by nlinarith)]
    have h4 : x ∈ A := by
      rw [hA]
      exact ⟨h2, h3⟩
    exact h4