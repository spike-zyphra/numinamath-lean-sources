import Mathlib

/- Find the solution to $x|x| = 2x+1$ which has the smallest value. -/
theorem algebra_10648 : IsLeast {(x : ℝ) | x * |x| = 2 * x + 1} (-1) := by
  simp only [IsLeast, lowerBounds]; simp
  refine ⟨ by ring_nf, ?_ ⟩
  intro a ha
  -- We consider two cases, $x$ is positive (so $|x| = x$), and $x$ is non postive (so $|x| = -x$).
  if ha0 : 0 < a then
    linarith
  else
    -- When $x<=0$ the equation becomes $x^2+2x+1=0$, so $(x+1)^2 = 0$ and $x=-1$.
    simp at ha0
    rw [show |a| = -a by exact abs_eq_neg_self.mpr ha0] at ha
    apply_fun (. + a * a) at ha; ring_nf at ha; symm at ha
    rw [show 1 + a * 2 + a ^ 2 = (a + 1) ^ 2 by ring_nf] at ha
    rw [sq_eq_zero_iff] at ha
    linarith
