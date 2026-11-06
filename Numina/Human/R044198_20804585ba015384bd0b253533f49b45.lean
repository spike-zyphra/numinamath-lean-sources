import Mathlib
/-
Bob can travel $m$ miles in $h$ hours on his bicycle. At this rate, how many hours would it take him to travel $h$ miles? Express your answer in terms of $m$ and $h$.-/
theorem algebra_21785 (m h v t: ℝ) (hm : 0 < m) (hh : 0 < h) (hv : v =  m / h) (ht : t = h / v):
    t = h ^ 2 / m := by
    --Since Bob travels $m$ miles in $h$ hours, he travels $m/h$ miles in 1 hour.  Therefore, in order to travel $h$ miles, he must travel for $h/(m/h) = \boxed{\frac{h^2}{m}}$ hours.
    --Substitute into the expression
    rw [hv] at ht; rw [ht];
    --Simplified expression
    field_simp; ring_nf
