import Mathlib

theorem algebra_293731 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (hf : ∀ x, f (x + 2) = -f x) (hf' : ∀ x ∈ Set.Icc 0 1, f x = 2 * x) :
    f (10 * Real.sqrt 3) = 36 - 20 * Real.sqrt 3 := by

  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h7 : f (10 * Real.sqrt 3) = - f (10 * Real.sqrt 3 - 2) := by
    have h8 : f (10 * Real.sqrt 3 - 2 + 2) = -f (10 * Real.sqrt 3 - 2) := hf (10 * Real.sqrt 3 - 2)
    ring_nf at h8 ⊢
    linarith [h8]
  have h8 : f (10 * Real.sqrt 3 - 2) = - f (10 * Real.sqrt 3 - 4) := by
    have h9 : f (10 * Real.sqrt 3 - 4 + 2) = -f (10 * Real.sqrt 3 - 4) := hf (10 * Real.sqrt 3 - 4)
    ring_nf at h9 ⊢
    linarith [h9]
  have h9 : f (10 * Real.sqrt 3 - 4) = - f (10 * Real.sqrt 3 - 6) := by
    have h10 : f (10 * Real.sqrt 3 - 6 + 2) = -f (10 * Real.sqrt 3 - 6) := hf (10 * Real.sqrt 3 - 6)
    ring_nf at h10 ⊢
    linarith [h10]
  have h10 : f (10 * Real.sqrt 3 - 6) = - f (10 * Real.sqrt 3 - 8) := by
    have h11 : f (10 * Real.sqrt 3 - 8 + 2) = -f (10 * Real.sqrt 3 - 8) := hf (10 * Real.sqrt 3 - 8)
    ring_nf at h11 ⊢
    linarith [h11]
  have h11 : f (10 * Real.sqrt 3 - 8) = - f (10 * Real.sqrt 3 - 10) := by
    have h12 : f (10 * Real.sqrt 3 - 10 + 2) = -f (10 * Real.sqrt 3 - 10) := hf (10 * Real.sqrt 3 - 10)
    ring_nf at h12 ⊢
    linarith [h12]
  have h12 : f (10 * Real.sqrt 3 - 10) = - f (10 * Real.sqrt 3 - 12) := by
    have h13 : f (10 * Real.sqrt 3 - 12 + 2) = -f (10 * Real.sqrt 3 - 12) := hf (10 * Real.sqrt 3 - 12)
    ring_nf at h13 ⊢
    linarith [h13]
  have h13 : f (10 * Real.sqrt 3 - 12) = - f (10 * Real.sqrt 3 - 14) := by
    have h14 : f (10 * Real.sqrt 3 - 14 + 2) = -f (10 * Real.sqrt 3 - 14) := hf (10 * Real.sqrt 3 - 14)
    ring_nf at h14 ⊢
    linarith [h14]
  have h14 : f (10 * Real.sqrt 3 - 14) = - f (10 * Real.sqrt 3 - 16) := by
    have h15 : f (10 * Real.sqrt 3 - 16 + 2) = -f (10 * Real.sqrt 3 - 16) := hf (10 * Real.sqrt 3 - 16)
    ring_nf at h15 ⊢
    linarith [h15]
  have h15 : f (10 * Real.sqrt 3 - 16) = - f (10 * Real.sqrt 3 - 18) := by
    have h16 : f (10 * Real.sqrt 3 - 18 + 2) = -f (10 * Real.sqrt 3 - 18) := hf (10 * Real.sqrt 3 - 18)
    ring_nf at h16 ⊢
    linarith [h16]
  have h16 : 0 ≤ 18 - 10 * Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h1]
  have h17 : 18 - 10 * Real.sqrt 3 ≤ 1 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h1]
  have h18 : f (18 - 10 * Real.sqrt 3) = 2 * (18 - 10 * Real.sqrt 3) := by
    apply hf' (18 - 10 * Real.sqrt 3) <;> 
      exact ⟨h16, h17⟩
  have h19 : f (10 * Real.sqrt 3 - 18) = -f (18 - 10 * Real.sqrt 3) := by
    have h20 : f (-(18 - 10 * Real.sqrt 3)) = -f (18 - 10 * Real.sqrt 3) := hodd (18 - 10 * Real.sqrt 3)
    have h21 : -(18 - 10 * Real.sqrt 3) = 10 * Real.sqrt 3 - 18 := by ring_nf
    rw [h21] at h20 
    linarith [h20]
  linarith [h7, h8, h9, h10, h11, h12, h13, h14, h15, h19, h18]