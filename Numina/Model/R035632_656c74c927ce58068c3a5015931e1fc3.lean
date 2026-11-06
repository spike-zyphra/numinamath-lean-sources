import Mathlib


open Real


theorem algebra_10965 (r1 r2 : ℝ) (h1 : r1 = 24) (h2 : r2 = 8) (h3 : 2 * π * r1 * 32 = 2 * π * r2 * x) :
    x = 96 := by
  rw [h1, h2] at h3
  have eq1 : (24 * (32 : ℝ)) = (8 : ℝ) * x := by
    have h4 : 2 * π * (24 : ℝ) * (32 : ℝ) = 2 * π * (8 : ℝ) * x := by
      linarith [h3]
    -- Now, the equation is 2 * π * 24 * 32 = 2 * π * 8 * x. We can divide both sides by 2 * π since π ≠ 0.
    have eq2 : (24 * (32 : ℝ)) = (8 : ℝ) * x := by
      have h5 : 2 * π * (24 * 32 : ℝ) = 2 * π * (8 * x : ℝ) := by
        linarith [h4]
      -- Now apply division on both sides.
      have h6 : (24 * (32 : ℝ)) = (8 : ℝ) * x := by
        have h7 : 2 * π * (24 * 32 : ℝ) = 2 * π * (8 * x : ℝ) := h5
        have eq3 : (24 * (32 : ℝ)) = (8 : ℝ) * x := by
          have h7 : 2 * π * (24 * 32 : ℝ) = 2 * π * (8 * x : ℝ) := h5
          have eq3 : 2 * π * ((24 * 32 : ℝ) - (8 * x : ℝ)) = 0 := by
            ring_nf at h7 ⊢
            linarith
          cases' (mul_eq_zero.1 eq3) with h7 h8
          · -- Case where 2 * π = 0, which is false since π > 0
            exfalso
            have h8 : π = 0 := by
              linarith
            linarith [Real.pi_pos, h8]
          · -- Case where (24 * 32) - (8 * x) = 0
            linarith
        linarith
      linarith
    linarith
  -- Now we have the equation without π.
  have hx2 : x = 96 := by
    have eq2 : (8 : ℝ) * x = (24 * 32 : ℝ) := by
      linarith [eq1]
    have h3 : (8 : ℝ) ≠ 0 := by norm_num
    have eq3 : x = ((24 * 32) / (8 : ℝ)) := by
      field_simp at eq2 ⊢
      linarith [eq2]
    have hx : x = 96 := by
      rw [eq3]
      norm_num
    exact hx
  exact hx2