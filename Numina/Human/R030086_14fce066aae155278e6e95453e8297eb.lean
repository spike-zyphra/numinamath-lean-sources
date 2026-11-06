import Mathlib

/- The length of a rectangle is three times its width. Given that its perimeter and
   area are both numerically equal to $k>0$, find $k$. -/
theorem algebra_609728 (a b k: ℝ) (hk: k > 0) (hab: b = 3 * a)
    (hk_area: k = a * b) (hk_per: k = 2 * (a + b)): k = (64: ℝ) / 3 := by
  --  Let $a$ be the width of the rectangle. Then the length of the rectangle is $3 a$, so the perimeter is $2(a+3 a)=8 a$,
  rw [hk_per, hab] at hk_area
  -- so the perimeter is $2(a+3 a)=8 a$, and the area is $3 a^{2}$
  -- Since the length is numerically equal to the width, we know that $$ 8 a=3 a^{2}=k $$
  ring_nf at hk_area
  rw [pow_two a, mul_assoc a a 3] at hk_area
  -- Because $k&gt;0$, the rectangle is non-degenerate. It follows that $8 = 3a$
  have := (mul_right_inj' (show a ≠ 0 by linarith)).mp hk_area
  -- So $a = 8 / 3$
  have : a = 8 / 3 := by linarith
  -- Therefore, $k=\frac{64}{3}$.
  rw [hab, this] at hk_per
  norm_num at hk_per
  exact hk_per
