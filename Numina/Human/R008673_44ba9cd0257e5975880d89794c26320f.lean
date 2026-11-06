import Mathlib

/- For the one-variable quadratic equation $x^{2}+x-4m=0$ to have real roots, the range of $m$ is ____. -/
theorem algebra_9135 (m : ℝ) : (∃ x : ℝ, x^2 + x - 4 * m = 0) ↔ m ≥ -1 / 16 := by
  have diseq: discrim (1:ℝ) 1 (-4*m) = 1+16*m := by
    rw [discrim]
    ring
  have hdis: 0 ≤ discrim (1:ℝ) 1 (-4*m) ↔ m ≥ (-1:ℝ)/16  := by
    rw [diseq]
    constructor
    intro h; linarith [h]
    intro h; linarith [h]
  rw [← hdis]
  have pos1: (1:ℝ) ≠ 0 := by norm_num
  constructor
  -- quadratic has roots → discrim equal square
  intro h
  rcases h with ⟨x0,hx0⟩
  have h1: discrim (1:ℝ) 1 (-4*m) = (2*1*x0+1)^2 := by
    have hx0': 1 * (x0 * x0) + 1 * x0 + -4 * m = 0 := by
      rw [← hx0]; ring
    apply (quadratic_eq_zero_iff_discrim_eq_sq pos1 x0).mp hx0'
  rw [h1]
  exact sq_nonneg (2 * 1 * x0 + 1)
  -- discrim nonneg → exists rooot
  intro h
  have h1: ∃s, discrim (1:ℝ) 1 (-4*m) = s*s := by
    use √(discrim (1:ℝ) 1 (-4*m))
    exact Eq.symm (Real.mul_self_sqrt h)
  have h2: (∃ x : ℝ, x^2 + x - 4 * m = 0) ↔ (∃x:ℝ, 1*(x*x)+1*x + -4*m=0) := by
    constructor
    rintro ⟨x0, hx0⟩
    use x0
    rw [← hx0]; ring
    rintro ⟨x0, hx0⟩
    use x0
    rw [← hx0]; ring
  rw [h2]
  apply exists_quadratic_eq_zero pos1 h1
