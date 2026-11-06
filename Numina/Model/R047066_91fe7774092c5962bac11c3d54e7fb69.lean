import Mathlib
open Real
theorem algebra_608310 (x y : ℝ) (h1 : x + sin y = 2008) (h2 : x + 2008 * cos y = 2007) (h3 : 0 ≤ y ∧ y ≤ π / 2) : x + y = 2007+ π / 2:= by
  have h4 : sin y - 2008 * cos y = 1 := by
    nlinarith 
  have h5 : 0 ≤ y := h3.1
  have h6 : y ≤ π / 2 := h3.2
  have h7 : cos y ≥ 0 := by
    apply cos_nonneg_of_neg_pi_div_two_le_of_le
    linarith [h5, Real.pi_pos]
    linarith [h6, Real.pi_pos]
  have h8 : sin y ≥ 0 := by
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith [h5, Real.pi_pos]
    linarith [h6, Real.pi_pos]
  -- From h4: `sin y - 2008 * cos y = 1`, we can rearrange to `sin y - 1 = 2008 * cos y`.
  -- Since the left side `sin y - 1 <= 0` as `sin y <= 1`.
  -- The right side `2008 * cos y >= 0` since `cos y >= 0`.
  -- Thus equality holds only if both sides are zero.
  have h9 : cos y = 0 := by 
    have h11 : sin y ≤ 1 := by 
      linarith [Real.sin_le_one y]
    nlinarith [Real.sin_sq_add_cos_sq y, h7, h11, h4, h8]
  have h10 : y = π / 2 := by 
    have h18 : y ≥ π / 2 := by
      by_contra h
      push_neg at h 
      have h17 : y < π / 2 := by linarith 
      -- Now we show cos y > 0 from y < π/2.
      have h15 : cos y > 0 := by
        apply cos_pos_of_mem_Ioo 
        constructor 
        · nlinarith [h17, Real.pi_pos] 
        · nlinarith [h17, Real.pi_pos]
      -- Now with cos y = 0 (from h9) and cos y > 0 (from h15).
      linarith [h9, h15] 
    have h19 : y ≤ π / 2 := h6 
    have h20 : y = π / 2 := by linarith [h18, h19]
    exact h20 
  -- Now that we know $y = \pi/2$, we can compute $x$ from h1.
  have h11 : sin y = 1 := by 
    rw [h10] 
    norm_num 
  -- From h1: `x + sin y = 2008`, with `sin y = 1`:
  -- `x + 1 = 2008` implies `x = 2007`.
  have hx : x = 2007 := by 
    linarith [h11, h1]
  linarith [hx, h10, Real.pi_pos]