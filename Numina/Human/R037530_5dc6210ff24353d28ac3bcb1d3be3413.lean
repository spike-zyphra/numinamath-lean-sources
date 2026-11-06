import Mathlib

/- Determine all positive real numbers $x$ and $y$ satisfying the equation
$$
x+y+\frac{1}{x}+\frac{1}{y}+4=2 \cdot(\sqrt{2 x+1}+\sqrt{2 y+1}) .
$$ -/
theorem algebra_240460 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x + y + 1 / x + 1 / y + 4 = 2 * (Real.sqrt (2 * x + 1) + Real.sqrt (2 * y + 1)) ↔
    (x = 1 + Real.sqrt 2 ∧ y = 1 + Real.sqrt 2) := by
  constructor
  · intro h
    -- Note that $$ x+\frac{1}{x}+2-2 \sqrt{2 x+1}=\frac{x^{2}+2 x+1-2 x \sqrt{2 x+1}}{x}=\frac{1}{x}(x-\sqrt{2 x+1})^{2}. $$
    have hlemma (x: ℝ) (hx: x > 0) : x + 1 / x + 2 - 2 * √ (2 * x + 1) = (x - √ (2 * x + 1)) ^ 2 / x := by
      ring_nf
      field_simp
      ring_nf
    have hx_lemma := hlemma x hx
    have hy_lemma := hlemma y hy
    -- Hence the original equation can be rewritten as
    -- $$ \frac{1}{x}(x-\sqrt{2 x+1})^{2}+\frac{1}{y}(y-\sqrt{2 y+1})^{2}=0 . $$
    have h2 := sub_eq_zero.mpr h
    have h3 : x + 1 / x + 2 - 2 * √ (2 * x + 1) + (y + 1 / y + 2 - 2 * √ (2 * y + 1)) = 0 := by linarith [h2]
    rw [hx_lemma, hy_lemma] at h3
    have hx_part_nonneg : (x - √(2 * x + 1)) ^ 2 / x ≥ 0 := by positivity
    have hy_part_nonneg : (y - √(2 * y + 1)) ^ 2 / y ≥ 0 := by positivity
    -- For $x, y \gt 0$, this gives $x-\sqrt{2 x+1}=0$ and $y-\sqrt{2 y+1}$. 
    have hboth_zero := (add_eq_zero_iff_of_nonneg hx_part_nonneg hy_part_nonneg).mp h3
    simp at hboth_zero
    -- It follows that the only solution is $x=y=1+\sqrt{2}$.
    have hx_near_sol : x = √(2 * x + 1) := by
      apply sub_eq_zero.mp
      have : ¬ x = 0 := by linarith [hx]
      exact (or_iff_right this).mp (Or.symm hboth_zero.1)
      -- Since $x > 0$, $x$ is impossible to be 1 - √2.
    have hy_near_sol : y = √(2 * y + 1) := by
      apply sub_eq_zero.mp
      have : ¬ y = 0 := by linarith [hy]
      exact (or_iff_right this).mp (Or.symm hboth_zero.2)
    have hx_sol : x = √ 2 + 1 := by
      have := congrFun (congrArg HPow.hPow hx_near_sol) 2
      rw [Real.sq_sqrt] at this
      have : (x - 1) ^ 2 = 2 := by linarith [this]
      have h_sqrt : (x - 1) ^ 2 = (√ 2) ^ 2 := by
        rw [this]
        apply (Eq.symm (Real.sq_sqrt _))
        simp
      have h_eq := eq_or_eq_neg_of_sq_eq_sq _ _ h_sqrt
      have h_nonneg_sol : ¬ x - 1 = -√2 := by
        by_contra! hcx
        have : x = 1 - √ 2 := by linarith
        have : 1 < √ 2 := by
          by_contra! h
          have : ¬ 1^2 ≥ (√ 2)^2 := by simp
          have : 1^2 ≥ (√ 2)^2 := by
            apply pow_le_pow_left₀ (by simp) h
          contradiction
        have : ¬ x > 0 := by linarith
        contradiction
      have h_eq_onecase := (or_iff_right h_nonneg_sol).mp (Or.symm h_eq)
      linarith
      positivity
    have hy_sol : y = √ 2 + 1 := by
      have := congrFun (congrArg HPow.hPow hy_near_sol) 2
      rw [Real.sq_sqrt] at this
      have : (y - 1) ^ 2 = 2 := by linarith [this]
      have h_sqrt : (y - 1) ^ 2 = (√ 2) ^ 2 := by
        rw [this]
        apply (Eq.symm (Real.sq_sqrt _))
        simp
      have h_eq := eq_or_eq_neg_of_sq_eq_sq _ _ h_sqrt
      -- Since $y > 0$, $y$ is impossible to be 1 - √2.
      have h_nonneg_sol : ¬ y - 1 = -√2 := by
        by_contra! hcx
        have : y = 1 - √ 2 := by linarith
        have : 1 < √ 2 := by
          by_contra! h
          have : ¬ 1^2 ≥ (√ 2)^2 := by simp
          have : 1^2 ≥ (√ 2)^2 := by
            apply pow_le_pow_left₀ (by simp) h
          contradiction
        have : ¬ y > 0 := by linarith
        contradiction
      have h_eq_onecase := (or_iff_right h_nonneg_sol).mp (Or.symm h_eq)
      linarith
      positivity
    apply And.intro
    linarith
    linarith
  · intro h
    -- Substitute back to verify it satisfies the condition.
    obtain ⟨hx_sol, hy_sol⟩ := h
    rw [hx_sol, hy_sol]
    field_simp
    ring_nf
    field_simp
    ring_nf
    have : 3 + √2 * 2 = (1 + √ 2) ^ 2 := by
      ring_nf
      rw [Real.sq_sqrt]
      ring_nf
      simp
    rw [this]
    field_simp
    ring_nf
    rw [Real.sq_sqrt, show 2 * 4 = (8: ℝ) by ring]
    ring
    positivity
