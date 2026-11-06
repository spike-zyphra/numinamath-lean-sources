import Mathlib

theorem algebra_1138 {x : ℝ} (hx : 0 < x) (h : (12 - x) * (8 - x) = x * x) :
    x = 4.8 := by
  -- Equation expansion: $(12 - x)(8 - x) = x * x$
  -- Expanding and simplifying: $96 - 20x = 0$
  -- Solving for x: $96 = 20x$, so $x = 96/20 = 4.8$
  -- In Lean, converting 96/20 to 4.8 using norm_num

  nlinarith
  <;> ring_nf at h ⊢ <;> nlinarith