import Mathlib

/- Let $a,$ $b,$ $c$ be nonnegative real numbers such that $a + b + c = 1.$  Find the maximum value of
\[\frac{ab}{a + b} + \frac{ac}{a + c} + \frac{bc}{b + c}.\] -/
theorem algebra_12695 : IsGreatest {x : ℝ | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
    a + b + c = 1 ∧ x = a * b / (a + b) + a * c / (a + c) + b * c / (b + c)} (1 / 2) := by

  -- by AM-HM, (a+b)/2 ≥ 2/(1/a + 1/b) = 2ab / (a+b)
  -- or, ab/(a+b) ≤ (a+b)/4
  have ineq {a b: ℝ} (ha: a ≥ 0) (hb: b ≥ 0): a*b / (a+b) ≤ (a+b) / 4 := by
    by_cases hha: a = 0
    · simp only [hha, zero_mul, zero_add, zero_div]
      positivity
    by_cases hhb: b = 0
    · simp only [hhb, mul_zero, add_zero, zero_div]
      positivity
    replace ha: a > 0 := lt_of_le_of_ne ha (fun x => hha x.symm)
    replace hb: b > 0 := lt_of_le_of_ne hb (fun x => hhb x.symm)
    have hab: 0 < a+b := by linarith only [ha,hb]
    refine (div_le_iff₀ hab).mpr ?_
    linarith only [four_mul_le_sq_add a b]


  rw [IsGreatest, upperBounds]
  simp only [exists_and_left, one_div, Set.mem_setOf_eq,
  forall_exists_index, and_imp]

  constructor

  · -- reach maximum when a=b=c=1/3
    use 1/3
    refine ⟨(by norm_num), ?_⟩
    use 1/3
    refine ⟨(by norm_num), ?_⟩
    use 1/3
    norm_num

  · -- show 1/2 is upper bound.
    rintro _ a ha b hb c hc habc rfl
    have h1 := ineq ha hb
    have h2 := ineq ha hc
    have h3 := ineq hb hc
    linarith only [h1,h2,h3,habc]