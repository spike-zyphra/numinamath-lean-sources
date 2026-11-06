import Mathlib

theorem algebra_13877 {f : ℝ → ℝ} (h : ∀ x, f (x + 2) = -f x ∧ f (-x) = -f x)
    (h' : ∀ x ∈ Set.Ioo 0 1, f x = 2 * x) :
    f (10 * Real.sqrt 3) = 36 - 20 * Real.sqrt 3 := by

  have h1 : ∀ x, f (x + 2) = -f x := by
    intro x
    exact (h x).1

  have h2 : ∀ x, f (-x) = -f x := by
    intro x
    exact (h x).2

  have h3 : f (10 * Real.sqrt 3) = f (10 * Real.sqrt 3 - 16) := by
    have h5 : f (10 * Real.sqrt 3) = -f (10 * Real.sqrt 3 - 2) := by
      specialize h1 (10 * Real.sqrt 3 - 2)
      ring_nf at h1 ⊢
      linarith
    have h6 : f (10 * Real.sqrt 3 - 2) = -f (10 * Real.sqrt 3 - 4) := by
      specialize h1 (10 * Real.sqrt 3 - 4)
      ring_nf at h1 ⊢
      linarith
    have h7 : f (10 * Real.sqrt 3 - 4) = -f (10 * Real.sqrt 3 - 6) := by
      specialize h1 (10 * Real.sqrt 3 - 6)
      ring_nf at h1 ⊢
      linarith
    have h8 : f (10 * Real.sqrt 3 - 6) = -f (10 * Real.sqrt 3 - 8) := by
      specialize h1 (10 * Real.sqrt 3 - 8)
      ring_nf at h1 ⊢
      linarith
    have h9 : f (10 * Real.sqrt 3 - 8) = -f (10 * Real.sqrt 3 - 10) := by
      specialize h1 (10 * Real.sqrt 3 - 10)
      ring_nf at h1 ⊢
      linarith
    have h10 : f (10 * Real.sqrt 3 - 10) = -f (10 * Real.sqrt 3 - 12) := by
      specialize h1 (10 * Real.sqrt 3 - 12)
      ring_nf at h1 ⊢
      linarith
    have h11 : f (10 * Real.sqrt 3 - 12) = -f (10 * Real.sqrt 3 - 14) := by
      specialize h1 (10 * Real.sqrt 3 - 14)
      ring_nf at h1 ⊢
      linarith
    have h12 : f (10 * Real.sqrt 3 - 14) = -f (10 * Real.sqrt 3 - 16) := by
      specialize h1 (10 * Real.sqrt 3 - 16)
      ring_nf at h1 ⊢
      linarith
    linarith [h5, h6, h7, h8, h9, h10, h11, h12]

  have h4 : f (10 * Real.sqrt 3 - 16) = -f (10 * Real.sqrt 3 - 18) := by
    specialize h1 (10 * Real.sqrt 3 - 18)
    ring_nf at h1 ⊢
    linarith

  have h5 : f (10 * Real.sqrt 3 - 18) = -f (18 - 10 * Real.sqrt 3) := by
    specialize h2 (10 * Real.sqrt 3 - 18)
    have h7 : - (10 * Real.sqrt 3 - 18) = 18 - 10 * Real.sqrt 3 := by ring
    rw [h7] at h2
    linarith

  have h8 : 0 < 18 - 10 * Real.sqrt 3 ∧ 18 - 10 * Real.sqrt 3 < 1 := by
    have h8_1 : 0 < 18 - 10 * Real.sqrt 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h8_2 : 18 - 10 * Real.sqrt 3 < 1 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    exact ⟨h8_1, h8_2⟩

  have h9 : f (18 - 10 * Real.sqrt 3) = 2 * (18 - 10 * Real.sqrt 3) := by
    apply h'
    exact h8

  rw [h3, h4, h5, h9]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]