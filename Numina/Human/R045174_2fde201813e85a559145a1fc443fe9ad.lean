import Mathlib

/- The graph of the equation $y=ax^2+bx-6$ is completely below the $x$-axis.
If $a^2=49$, what is the largest possible integral value of $b$? -/
theorem algebra_20171:
  IsGreatest {b | ∃a:ℝ, (a^2=49 ∧ (∀x:ℝ, a*x^2+b*x-6 < 0) ∧ ∃m:ℤ, b=m)} 12 := by
  -- y=ax^2+bx-6 is completely below x-axis, so ax^2+bx-6 < 0 for any x
  -- therefore equation ax^2+bx-6 has no solution, and discrim must < 0
  have h1{a:ℝ}(ha:a^2=49)(b:ℝ)(h: ∀x:ℝ, a*x^2+b*x-6<0): discrim a b (-6) < 0 := by
    by_contra! hc
    have anz: a ≠ 0 := by
      by_contra! az; rw [az] at ha; simp at ha
    have hh1: √(discrim a b (-6)) * √(discrim a b (-6)) = discrim a b (-6) := by
      exact Real.mul_self_sqrt hc
    have hh2: ∃x:ℝ, a*(x*x) + b*x + (-6) = 0 := by
      apply exists_quadratic_eq_zero anz
      use √(discrim a b (-6)); simp [hh1]
    rcases hh2 with ⟨x,hx⟩
    have nhx := h x
    rw [← hx] at nhx; simp [pow_two, mul_assoc] at nhx
  -- that is to say, b^2-4ac = b^2+24a < 0, or b^2 < -24a
  have h2{a:ℝ}(ha:a^2=49)(b:ℝ)(h: ∀x:ℝ, a*x^2+b*x-6<0): b^2 < -24*a := by
    have := h1 ha b h
    rw [discrim] at this; simp at this
    linarith [this]
  -- combine with a^2 = 49, we solve b^2 < 168. 13^2=169, so b < 13
  have aeq{a:ℝ}(ha:a^2=49)(b:ℝ)(h: ∀x:ℝ, a*x^2+b*x-6<0): a = -7 := by
    have: a = 7 ∨ a = -7 := by
      apply mul_self_eq_mul_self_iff.mp
      simp [← pow_two, ha]; norm_num
    rcases this with hl | hr
    · have := h2 ha b h
      rw [hl] at this; simp at this
      have hh1: b^2 < 0 := by
        apply lt_trans this (by norm_num)
      have hh2: 0 ≤ b^2 := sq_nonneg b
      exfalso; linarith [hh1, hh2]
    · exact hr
  have h3{a:ℝ}(ha:a^2=49)(b:ℝ)(h: ∀x:ℝ, a*x^2+b*x-6<0): b < 13 := by
    have := h2 ha b h
    rw [aeq ha b h] at this; norm_num at this
    nlinarith [this]
  -- thus we can solve the problem
  rw [IsGreatest, upperBounds]; simp; constructor
  · use -7; norm_num;
    constructor
    · intro x
      have hh1: 7*x^2 - 12*x + 6 > 0 := by
        have: 7*x^2 - 12*x + 6 = 7*(x-6/7)^2 + 6/7 := by ring
        rw [this]; linarith [sq_nonneg (x-6/7)]
      linarith [hh1]
    · use 12; simp
  · intro b a ha h' m hb
    rw [hb]; norm_cast
    have: m < 13 := by
      have: (m:ℝ) < 13 := by
        rw [← hb]
        apply h3 ha b
        intro x
        linarith [h' x]
      norm_cast at this
    exact Int.lt_add_one_iff.mp this
