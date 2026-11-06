import Mathlib

/- Determine which of the following numbers is smallest in value: $54 \sqrt{3}, 144,108 \sqrt{6}-108 \sqrt{2}$. -/
theorem algebra_608906: IsLeast {54 * √3, 144, 108 * √6 - 108 * √2} (54 * √3) := by
  unfold IsLeast lowerBounds
  simp
  constructor
  . -- 54 * √3 < 144
    -- Square both sides of the equation simultaneously.
    rw [
      <-abs_of_pos (show 0 < 54 * √3 from mul_pos (by norm_num) (by simp)),
      <-abs_of_pos (show 0 < (144:ℝ) by norm_num),
      <-sq_le_sq,
      mul_pow,
      Real.sq_sqrt (by norm_num)
    ]
    norm_num
  . -- 54 * 2 * (√6 - √2) < 54 * 2 * √6
    -- divide by 54
    rw [show 108 * √6 - 108 * √2 = 54 * (2 * (√6 - √2)) by ring]
    apply flip mul_le_mul_of_nonneg_left (by norm_num)
    -- Square both sides of the equation simultaneously.
    rw [
      <-abs_of_pos (show 0 < √3 by simp),
      <-abs_of_pos (show 0 < 2 * (√6 - √2) from mul_pos (by norm_num) (by simp; norm_num)),
      <-sq_le_sq
    ]
    -- move sqrt to one side
    ring_nf
    repeat rw [Real.sq_sqrt (by norm_num)]
    rw [<-Real.sqrt_mul (by norm_num), <-sub_nonneg]
    ring_nf
    -- square again
    rw [sub_nonneg,
      <-abs_of_pos (show 0 < (29:ℝ) by simp),
      <-abs_of_pos (show 0 < √12 * 8 from mul_pos (by norm_num) (by norm_num)),
      <-sq_le_sq,
      mul_pow,
      Real.sq_sqrt (by norm_num)
    ]
    norm_num
