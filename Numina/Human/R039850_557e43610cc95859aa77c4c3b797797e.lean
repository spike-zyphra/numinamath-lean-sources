import Mathlib

/-Find the product of the $y$-coordinates of all the distinct solutions $(x,y)$ for the two equations $y=x^2-8$ and $y^2=-5x+44$.-/
theorem algebra_21372 : ∏ᶠ x ∈ {(x, y) : ℝ × ℝ | y = x^2 - 8 ∧ y^2 = -5*x + 44}, x.2 = 1736 := by
  -- we only need to prove that the required set equals {(-4,8), (-1,-7), ((5 + √5)/2,(-1+5*√5)/2), ((5 - √5)/2, (-1-5*√5)/2)}
  suffices {(x, y) : ℝ × ℝ | y = x^2 - 8 ∧ y^2 = -5*x + 44} = {(-4,8), (-1,-7), ((5 + √5)/2,(-1+5*√5)/2), ((5 - √5)/2, (-1-5*√5)/2)} by
    rw [this]
    repeat
      rw [finprod_mem_insert]
    rw [finprod_mem_singleton]
    norm_num
    field_simp
    rw [←sq_sub_sq, mul_pow, Real.sq_sqrt]
    norm_num
    all_goals norm_num
    all_goals field_simp
    · intro h
      linarith [Real.sqrt_pos.2 (show 0 < 5 by simp)]
    · split_ands <;> intro h
      · linarith [Real.sqrt_pos.2 (show 0 < 5 by simp)]
      · have : √5 < √9 := Real.sqrt_lt_sqrt (by simp) (by norm_num)
        linarith
    · split_ands <;> intro h
      · linarith [Real.sqrt_pos.2 (show 0 < 5 by simp)]
      · have : √5 < √9 := Real.sqrt_lt_sqrt (by simp) (by norm_num)
        linarith
  ext ⟨x, y⟩
  simp
  constructor
  · intro ⟨h1, h2⟩
    -- Squaring $y=x^2-8$, we obtain $y^2=x^4-16x^2+64$. Setting the right-hand sides equal to each other, we find \begin{align*}
    -- -5x+44&=x^4-16x^2+64\quad\Rightarrow\\
    -- 0&=x^4-16x^2+5x+20\quad\Rightarrow\\
    -- &=x^2(x^2-16)+5(x+4)\quad\Rightarrow\\
    -- &=x^2(x-4)(x+4)+5(x+4)\quad\Rightarrow\\
    -- &=(x+4)(x^3-4x^2+5).
    have hx : (x + 4) * (x + 1) * (x^2 - 5*x + 5) = 0 := by nlinarith
    -- Because $x^2-5x+5$ does not factor easily, we use the quadratic formula to get \begin{align*}
    -- x&=\frac{5\pm\sqrt{25-4\cdot1\cdot5}}{2}\quad\Rightarrow\\
    -- &=\frac{5\pm\sqrt{5}}{2}.
    -- \end{align*} The four values for $x$ are then $-4, -1, \frac{5\pm\sqrt{5}}{2}$. Therefore, the four solutions are $$(-4,8),(-1,-7),$$ $$\left(\frac{5+\sqrt{5}}{2},\frac{-1+5\sqrt{5}}{2}\right),\left(\frac{5-\sqrt{5}}{2},\frac{-1-5\sqrt{5}}{2}\right).$$
    apply mul_eq_zero.1 at hx
    rcases hx with hl | hr
    · apply mul_eq_zero.1 at hl
      rcases hl with hl | hl
      · left; exact ⟨by linarith, by nlinarith⟩
      · right; left; exact ⟨by linarith, by nlinarith⟩
    have hdisc : discrim 1 (-5) 5 = √5 * √5 := by norm_num [discrim]
    have hx := (quadratic_eq_zero_iff (by simp) hdisc x).1 (by nlinarith)
    rcases hx with hx | hx
    · right; right; left; exact ⟨by norm_num [hx], by
      norm_num [hx, h1]; field_simp; norm_num [add_sq]
      ring_nf
      ⟩
    · right; right; right
      exact ⟨by norm_num [hx], by norm_num [hx, h1]; field_simp; norm_num [sub_sq]; ring_nf⟩
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num [add_sq, sub_sq, mul_pow] <;> ring_nf
    norm_num; ring_nf; tauto
    norm_num; ring_nf; tauto