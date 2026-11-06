import Mathlib

/-Find all solutions to the equation $$(z^2 - 3z + 1)^2 - 3(z^2 - 3z + 1) + 1 = z.$$-/
theorem algebra_22449 (z : ℝ) :
    (z^2 - 3 * z + 1)^2 - 3 * (z^2 - 3 * z + 1) + 1 = z ↔
    z = 1 + Real.sqrt 2 ∨ z = 1 - Real.sqrt 2 ∨ z = 2 + Real.sqrt 3 ∨ z = 2 - Real.sqrt 3 := by
  obtain ⟨y, hy⟩ := show ∃y, y = z^2 - 3 * z + 1 by simp
  -- The expression $z^2-3z+1$ appears twice in the equation we're trying to solve. This suggests that we should try the substitution $y=z^2-3z+1$. Applying this to the left side of our original equation, we get y^2-3y+1=z
  constructor
  · -- which, interestingly, looks just like the substitution we made except that the variables are reversed. Thus we have a symmetric system of equations:
    -- \begin{align*}
    -- y &= z^2-3z+1, \\
    -- y^2-3y+1 &= z.
    -- \end{align*}
    -- Adding these two equations gives us
    -- $$y^2-2y+1 = z^2-2z+1,$$which looks promising as each side can be factored as a perfect square:
    -- $$(y-1)^2 = (z-1)^2.$$It follows that either $y-1 = z-1$ (and so $y=z$), or $y-1 = -(z-1)$ (and so $y=2-z$). We consider each of these two cases.
    intro hz
    have : (y - 1)^2 = (z - 1)^2 := by
      have : y + (y^2 - 3 * y + 1) = z + (z^2 - 3 * z + 1) := by
        rw [hy.symm] at hz
        rw [hz, add_comm]
        simp
        exact hy
      linarith
    rw [sq_eq_sq_iff_abs_eq_abs, abs_eq_abs] at this
    obtain (r | r) := this
    · -- If $y=z$, then we have $z = z^2-3z+1$, and so $0 = z^2-4z+1$. Solving this quadratic yields $z=\frac{4\pm\sqrt{12}}2 = 2\pm\sqrt 3$.
      have : (z - (2 + √3)) * (z - (2 - √3)) = 0 := by
        ring_nf
        rw [Real.sq_sqrt (by positivity)]
        linarith
      simp at this
      obtain (r | r) := this
      · -- r: z - (2 + √3) = 0
        apply Or.inr (Or.inr (Or.inl _))
        linarith
      · -- r: z - (2 - √3) = 0
        apply Or.inr (Or.inr (Or.inr _))
        linarith
    · -- If $y=2-z$, then we have $2-z = z^2-3z+1$, and so $2 = z^2-2z+1 = (z-1)^2$. Thus we have $z-1=\pm\sqrt 2$, and $z=1\pm\sqrt 2$.
      have : (z - (1 + √2)) * (z - (1 - √2)) = 0 := by
        ring_nf
        rw [Real.sq_sqrt (by positivity)]
        linarith
      simp at this
      obtain (r | r) := this
      · -- r: z - (1 - √2) = 0
        apply Or.inl _
        linarith
      · -- r: z - (1 + √2) = 0
        apply Or.inr (Or.inl _)
        linarith
    -- Putting our two cases together, we have four solutions in all: $z=\boxed{1+\sqrt 2,\ 1-\sqrt 2,\ 2+\sqrt 3,\ 2-\sqrt 3}$.
  · have sqrt_2_pow_2 : √2 ^ 2 = 2 := by simp
    have sqrt_2_pow_3 : √2 ^ 3 = 2 * √2 := by rw [pow_succ, sqrt_2_pow_2]
    have sqrt_2_pow_4 : √2 ^ 4 = 4 := by
      rw [show 4 = 2 + 2 by simp, pow_add, sqrt_2_pow_2]
      norm_num
    have sqrt_3_pow_2 : √3 ^ 2 = 3 := by simp
    have sqrt_3_pow_3 : √3 ^ 3 = 3 * √3 := by rw [pow_succ, sqrt_3_pow_2]
    have sqrt_3_pow_4 : √3 ^ 4 = 9 := by
      rw [show 4 = 2 + 2 by simp, pow_add, sqrt_3_pow_2]
      norm_num
    rintro (r | r | r | r)
    repeat rw [r]; ring_nf; simp only [sqrt_2_pow_2, sqrt_2_pow_3, sqrt_2_pow_4]; ring_nf
    repeat rw [r]; ring_nf; simp only [sqrt_3_pow_2, sqrt_3_pow_3, sqrt_3_pow_4]; ring_nf
