import Mathlib

/-- If x<0, then which of the following must be positive?
 A) $\frac{x}{|x|}$
 B) $-x^2$
 C) $-2^x$
 D) $-x^{-1}$
 E) $\sqrt[3]{x}$
 -/
theorem algebra_94128 (x : ℝ) (hx : x < 0) :
    ¬ x / |x| > 0 ∧
    ¬ - x^2 > 0 ∧
    ¬ - (2 : ℝ)^x > 0 ∧
    -(x^(-1 : ℝ)) > 0 := by
  split_ands
  · apply not_lt_of_gt
    -- $\frac{x}{|x|}$ is negative if x is negative and $|x|$ is positive
    rw[div_neg_iff]
    right
    -- the former holds by assumption
    refine ⟨hx,?g⟩
    -- the latter holds because $x < 0$
    apply abs_pos_of_neg hx
    -- $- x^{-1}$ is positive iff $x^{-1}$ is negative
  · apply not_lt_of_gt
    -- $-x^2 <0$ iff $x^2 >0$
    rw[neg_neg_iff_pos]
    -- which is true due to $x \ne 0$
    exact sq_pos_of_neg hx
  · apply not_lt_of_gt
    -- $-2^x <0$ iff $2^x >0$
    rw[neg_neg_iff_pos]
    -- which is true due to $2 > 0$
    apply Real.rpow_pos_of_pos (by simp)
  · apply neg_pos.mpr
    -- iff $x$ is negative
    rwa[Real.rpow_neg_one, inv_neg'']