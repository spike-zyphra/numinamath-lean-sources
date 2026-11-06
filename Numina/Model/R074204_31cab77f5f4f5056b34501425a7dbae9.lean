import Mathlib

theorem algebra_157890 (p : ℝ) (h : p ∈ Set.Icc 0 1) (h1 : 1 - (1 - p) ^ 3 = 0.875) :
    p = 0.5 := by
  have h2 : (1 - p) ^ 3 = 0.125 := by 
    have h_eq : (1 - (1 - p) ^ 3 : ℝ) = (0.875 : ℝ) := by linarith
    nlinarith
  have h3 : (1 - p) = 0.5 := by 
    have h4 : (1 - p : ℝ) ^ 3 - (0.125 : ℝ) = 0 := by 
      rw [h2]
      ring
    -- Note that (1-p)^3 - 0.125 = ((1-p)-0.5)(something positive). The (something positive) is a quadratic.
    have h5 : (1 - p - (0.5 : ℝ)) * ((1 - p + (0.5 : ℝ)) ^ 2 + (1 - p - (0.5 : ℝ)) * (1 - p + (0.5 : ℝ)) + (0.25 : ℝ)) = 0 := by
      ring_nf at h4 ⊢
      nlinarith [sq_nonneg ((1 - p - 0.5 : ℝ)), sq_nonneg ((1 - p + 0.5 : ℝ)), sq_nonneg ((1 - p : ℝ))]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case where the linear factor is zero, so 1-p-0.5=0
      have h8 : (1 - p - 0.5 : ℝ) = 0 := by 
        linarith 
      have h9 : (1 - p : ℝ) = 0.5 := by 
        linarith
      linarith 
    · -- Case where the quadratic factor is zero, show contradiction using constraint p in [0,1]
      have h8 : ((1 - p + (0.5 : ℝ)) ^ 2 + (1 - p - (0.5 : ℝ)) * (1 - p + (0.5 : ℝ)) + (0.25 : ℝ)) = 0 := by
        nlinarith 
      -- Show suricaba prove it's greater than zero
      nlinarith [sq_nonneg ((1 - p - (0.5 : ℝ)) : ℝ), sq_nonneg ((1 - p + (0.5 : ℝ)) : ℝ), 
                h.1, h.2]
  -- From (1-p) = 0.5 derive p = 0.5
  nlinarith