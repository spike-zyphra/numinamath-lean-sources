import Mathlib

/- The quadratic $x^2 + \frac{3}{2} x - 1$ has the following property: the roots, which are $\frac{1}{2}$ and $-2,$ are one less than the final two coefficients.  Find a quadratic with leading term $x^2$ such that the final two coefficients are both non-zero, and the roots are one more than these coefficients.  Enter the roots of this quadratic. -/
theorem algebra_21628 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hroots : {x | x^2 + a * x + b = 0} = {b + 1, a + 1}) :
    a+1 = 3 / 2 ∧ b+1 = -2 := by
  -- from the problem statement, we suppose the equation is x^2+ax+b, therefore two roots are a+1 and b+1.
  have h1: (a+1)^2+a*(a+1)+b = 0 := by
    have: a+1 ∈ {x | x^2 + a * x + b = 0} := by
      rw [hroots]; simp
    exact this
  have h2: (b+1)^2+a*(b+1)+b = 0 := by
    have: b+1 ∈ {x | x^2 + a * x + b = 0} := by
      rw [hroots]; simp
    exact this
  have h1': (a+1)*(a+1) - (-a)*(a+1)+b = 0 := by
    rw [← h1]; ring
  have h2': (b+1)*(b+1) - (-a)*(b+1)+b = 0 := by
    rw [← h2]; ring
  have aadd := vieta_formula_quadratic h1'
  have badd := vieta_formula_quadratic h2'
  -- use Vieta's formula.
  rcases aadd with ⟨d,hd⟩
  have deq: d = b+1 := by
    have hh1: d ∈ {x | x^2 + a * x + b = 0} := by
      simp; linarith [hd.left]
    rw [hroots] at hh1; simp at hh1
    by_cases hab: a = b
    · rw [hab] at hh1; tauto
    · push_neg at hab
      rcases badd with ⟨e,he⟩
      have hh2: e ∈ {x | x^2 + a * x + b = 0} := by
          simp; linarith [he.left]
      rw [hroots] at hh2; simp at hh2
      rcases hh2 with heb | hea
      · rcases hh1 with hdb | hda
        · tauto
        · have: a+1 + (a+1) = b+1 + (b+1) := by
            rw [hda] at hd
            rw [hd.right.left]; symm
            rw [heb] at he
            apply he.right.left
          have nhab: a = b := by linarith [this]
          linarith [hab, nhab]
      · have tt1: b+1 = -a -(a+1) := by
          have := he.right.left
          rw [hea] at this; linarith [this]
        have tt2: d = -a-(a+1) := by linarith [hd.right.left]
        rw [tt1,tt2]
  -- thus we can use Vieta's formula to calculate sum and product of two roots.
  have hadd: (a+1) + (b+1) = -a := by
    rw [← deq, hd.right.left]
  have hmul: (a+1)*(b+1) = b := by
    rw [← deq, hd.right.right]
  -- from the first equation, a+1 = -b/2
  have a_of_b: a+1 = -b/2 := by
    linarith [hadd]
  --substitute into second equation, we can solve b
  have beq: b = -3 := by
    rw [a_of_b] at hmul
    have: -(b+1)/2 = 1 := by
      have: -(b+1)/2 = (-b/2*(b+1))/b := by
        field_simp [hb]; ring
      rw [this, hmul]; simp [hb]
    linarith [this]
  -- thus a is also determined
  have aeq: a = 1/2 := by
    rw [beq] at a_of_b
    linarith [a_of_b]
  -- so two roots are a+1 and b+1, 3/2 and -2.
  rw [aeq, beq]; norm_num