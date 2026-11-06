import Mathlib

theorem algebra_216325 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x, f (x + 2) = -f x)
    (hf' : ∀ x ∈ Set.Icc 0 1, f x = 2 * x) :
    f (10 * Real.sqrt 3) = 36 - 20 * Real.sqrt 3 := by
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  have h2 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
  -- Apply the property f(x+2)=-f(x) to get from f(a) to f(a-16).
  have h3 : f (10 * Real.sqrt 3) = - f (10 * Real.sqrt 3 - 2) := by
    specialize hf (10 * Real.sqrt 3 - 2)
    rw [show (10 * Real.sqrt 3 - 2 : ℝ) + 2 = (10 * Real.sqrt 3 : ℝ) by ring] at hf
    linarith
  have h4 : f (10 * Real.sqrt 3 - 2) = - f (10 * Real.sqrt 3 - 4) := by
    specialize hf (10 * Real.sqrt 3 - 4)
    rw [show (10 * Real.sqrt 3 - 4 : ℝ) + 2 = (10 * Real.sqrt 3 - 2 : ℝ) by ring] at hf
    linarith
  have h5 : f (10 * Real.sqrt 3 - 4) = - f (10 * Real.sqrt 3 - 6) := by
    specialize hf (10 * Real.sqrt 3 - 6)
    rw [show (10 * Real.sqrt 3 - 6 : ℝ) + 2 = (10 * Real.sqrt 3 - 4 : ℝ) by ring] at hf
    linarith
  have h6 : f (10 * Real.sqrt 3 - 6) = - f (10 * Real.sqrt 3 - 8) := by
    specialize hf (10 * Real.sqrt 3 - 8)
    rw [show (10 * Real.sqrt 3 - 8 : ℝ) + 2 = (10 * Real.sqrt 3 - 6 : ℝ) by ring] at hf
    linarith
  have h7 : f (10 * Real.sqrt 3 - 8) = - f (10 * Real.sqrt 3 - 10) := by
    specialize hf (10 * Real.sqrt 3 - 10)
    rw [show (10 * Real.sqrt 3 - 10 : ℝ) + 2 = (10 * Real.sqrt 3 - 8 : ℝ) by ring] at hf
    linarith
  have h8 : f (10 * Real.sqrt 3 - 10) = - f (10 * Real.sqrt 3 - 12) := by
    specialize hf (10 * Real.sqrt 3 - 12)
    rw [show (10 * Real.sqrt 3 - 12 : ℝ) + 2 = (10 * Real.sqrt 3 - 10 : ℝ) by ring] at hf
    linarith
  have h9 : f (10 * Real.sqrt 3 - 12) = - f (10 * Real.sqrt 3 - 14) := by
    specialize hf (10 * Real.sqrt 3 - 14)
    rw [show (10 * Real.sqrt 3 - 14 : ℝ) + 2 = (10 * Real.sqrt 3 - 12 : ℝ) by ring] at hf
    linarith
  have h10 : f (10 * Real.sqrt 3 - 14) = - f (10 * Real.sqrt 3 - 16) := by
    specialize hf (10 * Real.sqrt 3 - 16)
    rw [show (10 * Real.sqrt 3 - 16 : ℝ) + 2 = (10 * Real.sqrt 3 - 14 : ℝ) by ring] at hf
    linarith
  -- Use the odd function property: f(10√3 - 16) = -f(16 - 10√3).
  have h16 : f (10 * Real.sqrt 3 - 16) = - f (16 - 10 * Real.sqrt 3) := by
    have h17 : f (10 * Real.sqrt 3 - 16) = - f (16 - 10 * Real.sqrt 3) := by
      have h18 : 10 * Real.sqrt 3 - 16 = - (16 - 10 * Real.sqrt 3) := by ring
      rw [h18]
      rw [hodd]
    linarith
  -- Since 16 - 10√3 < 0, we relate f(16 - 10√3) to f((16 - 10√3) + 2).
  have h18 : (16 - 10 * Real.sqrt 3 : ℝ) < 0 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  have h36 : f (16 - 10 * Real.sqrt 3) = - f ((16 - 10 * Real.sqrt 3 : ℝ) + 2) := by
    have h37 : (16 - 10 * Real.sqrt 3 : ℝ) + 2 < (2 : ℝ) := by 
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
    -- Since 16 - 10√3 < 0, we use f(x) = -f(x+2).
    have h45 : f ((16 - 10 * Real.sqrt 3 : ℝ) + 2) = - f ((16 - 10 * Real.sqrt 3 : ℝ) + 2 - 2) := by
      specialize hf ((16 - 10 * Real.sqrt 3 : ℝ) + 2 - 2)
      rw [show ((16 - 10 * Real.sqrt 3 : ℝ) + 2 - 2) + 2 = (16 - 10 * Real.sqrt 3 : ℝ) + 2 by ring] at hf
      linarith
    have h46 : (16 - 10 * Real.sqrt 3 : ℝ) + 2 - 2 = (16 - 10 * Real.sqrt 3 : ℝ) := by ring
    rw [h46] at h45
    linarith
  -- Since (16 - 10√3) + 2 is in [0,1], we can use the definition.
  have h37 : ((16 - 10 * Real.sqrt 3) + 2 : ℝ) ∈ Set.Icc (0 : ℝ) (1 : ℝ) := by
    constructor
    · -- Show 0 ≤ (16 - 10 * Real.sqrt 3) + 2
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
    · -- Show (16 - 10 * Real.sqrt 3) + 2 ≤ 1
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  -- Apply the definition for x ∈ [0,1].
  have h38 : f ((16 - 10 * Real.sqrt 3) + 2) = 2 * ((16 - 10 * Real.sqrt 3) + 2) := by
    apply hf'
    exact h37
  -- Substitute back through the chain of equalities.
  rw [h3, h4, h5, h6, h7, h8, h9, h10, h16, h36, h38]
  ring_nf