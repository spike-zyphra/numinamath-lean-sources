import Mathlib

/- If the quadratic $x^2+6mx+m$ has exactly one real root, find the positive value of $m$. -/
theorem algebra_21887 (m : ℝ) (mpos: 0 < m)
  (h1: ∃ x:ℝ, x^2+6*m*x+m=0)
  (h2 : ∀ x y : ℝ,
  x^2+6*m*x+m=0 ∧ y^2+6*m*y+m=0 → x=y) : m = 1 / 9 := by
  -- for different lean4 version, following eq' should be re-arranged, in order to use lemmas around quadratic equation.
  have eq'(x:ℝ): x^2+6*m*x+m=1*x*x+(6*m)*x+m := by ring
  -- the quadratic has root, so discriminant is nonnegative, or can be written in the square form
  have dis_sq: ∃s:ℝ, discrim 1 (6*m) m = s^2 := by
    rcases h1 with ⟨x,hx⟩
    rw [eq' x, mul_assoc] at hx
    have hh2: (1:ℝ) ≠ 0 := by norm_num
    have hh3 := (quadratic_eq_zero_iff_discrim_eq_sq hh2 x).mp hx
    apply Exists.intro; apply hh3
  -- the quadratic has only one root, so discriminant must be zero.
  have dis_zero: discrim 1 (6*m) m = 0 := by
    rcases h1 with ⟨x,hx⟩
    rw [eq' x] at hx
    rcases dis_sq with ⟨s,hs⟩
    rw [pow_two] at hs
    have hh1: (1:ℝ) ≠ 0 := by norm_num
    -- in fact, we know two roots of quadratic equation. and they must be equal.
    let x1 := (-(6 * m) + s) / (2 * 1)
    have x1_def: x1 = (-(6 * m) + s) / (2 * 1) := rfl
    let x2 := (-(6 * m) - s) / (2 * 1)
    have x2_def: x2 = (-(6 * m) - s) / (2 * 1) := rfl
    have hh2: x1 = x2 := by
      have x1eq: x1^2+6*m*x1+m=0 := by
        rw [eq' x1, mul_assoc]
        apply (quadratic_eq_zero_iff hh1 hs x1).mpr
        tauto
      have x2eq: x2^2+6*m*x2+m=0 := by
        rw [eq' x2, mul_assoc]
        apply (quadratic_eq_zero_iff hh1 hs x2).mpr
        tauto
      apply h2 x1 x2 ⟨x1eq, x2eq⟩
    have hh3: s = 0 := by
      rw [x1_def, x2_def] at hh2; simp at hh2
      have: -(6*m)+s = -(6*m)-s := by linarith
      linarith [this]
    rw [hs, hh3]; simp
  -- discriminant eq zero, we can determine m by solving this equation
  have hm: (4*m)*(9*m-1) = 0 := by
    rw [← dis_zero, discrim]
    ring
  -- so m = 0 or m = 1/9. since m is positive, only 1/9 satisfies. so m = 1/9
  have meq := mul_eq_zero.mp hm
  rcases meq with hm1 | hm2
  · have: m = 0 := by linarith [hm1]
    rw [this] at mpos; simp at mpos
  · linarith [hm2]
