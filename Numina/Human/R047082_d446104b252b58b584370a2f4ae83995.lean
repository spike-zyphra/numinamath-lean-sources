import Mathlib

/- The equation $x^2+ ax = -14$ has only integer solutions for $x$. If $a$ is a positive integer, what is the greatest possible value of $a$? -/
theorem algebra_14773:
  IsGreatest {a:ℤ | 0 < a ∧ ∀x:ℝ, (x^2+a*x = -14 → ∃z:ℤ, x = z)} 15 := by
  rw [IsGreatest, upperBounds]; simp
  constructor
  -- verify 15 satisfy the condition. it's the easy direction.
  intro x hx
  -- for x^2+15x=-14, solution is -1 and -14
  have h1: x = -1 ∨ x = -14 := by
    have ht1: x^2+15*x+14 = 0 := by
      rw [hx]; ring
    have ht2: x^2+15*x+14 = (x+1)*(x+14) := by ring
    rw [ht2] at ht1
    have ht3 := mul_eq_zero.mp ht1
    rcases ht3 with hl | hr
    · rw [← add_zero (-1), ← hl]; simp
    · rw [← add_zero (-14), ← hr]; simp
  rcases h1 with x1 | x14
  · use (-1); rw [x1]; simp
  · use (-14); rw [x14]; simp
  -- next, we move on to the hard direction.
  intro a ha h
  -- noticee that x^2+ax=x(x+a)=-14, then x and x+a must one be positive and one negative. and a is positive, therefore x < 0, x+a > 0.
  have negx: ∀x:ℝ, (x^2+a*x=-14 → x < 0) := by
    intro x hx
    have ht1: x^2+a*x = x * (a+x) := by ring
    have ht2: x * (a+x) < 0 := by
      rw [← ht1, hx]; norm_num
    have ht3: x < 0 ∨ (a+x) < 0 := by
      by_contra! hc
      have: 0 ≤  x * (a+x) := by
        apply mul_nonneg hc.left hc.right
      linarith [ht2, this]
    rcases ht3 with hl | hr
    · exact hl
    · have ht4: 0 < (a:ℝ) := by
        exact Int.cast_pos.mpr ha
      linarith [hr, ht4]
  -- since x(x+a)=-14, then x must divide 14
  have divx: ∀x:ℝ, (x^2+a*x=-14 → ∃ z:ℤ, z = x ∧ z ∣ 14) := by
    intro x hx
    have h1 := h x hx
    rcases h1 with ⟨z,hz⟩
    use z
    rw [hz]; simp
    use -(z+a)
    let ex1 := z*(z+a)+14
    have ex1_def: ex1 = z*(z+a)+14 := rfl
    have: ex1 = 0 := by
      by_contra! hc
      have hc1: (ex1:ℝ) ≠ 0 := by
        exact Int.cast_ne_zero.mpr hc
      have hc2: (ex1:ℝ) = 0 := by
        rw [ex1_def]; simp
        have: (14:ℝ) = - - 14 := by simp
        rw [this, ← hx, hz]; ring
      contradiction
    rw [← add_zero (z* -(z+a)), ← this, ex1_def]; ring
  -- if negative x divide 14, consider factors of 14, x can only be -1,-2,-7,-14.
  have xeq: ∀x:ℝ, (x^2+a*x=-14 → x=-1 ∨ x=-2 ∨ x=-7 ∨ x=-14) := by
    intro x hx
    rcases h x with h0
    have exint := h0 hx
    rcases exint with ⟨x_int, xinteq⟩
    have intxneg: x_int < 0 := by
      have xneg := negx x hx
      rw [xinteq] at xneg
      by_contra! hc
      have: 0 ≤ (x_int:ℝ) := Int.cast_nonneg.mpr hc
      linarith [xneg, this]
    have intxdiv: x_int ∣ 14 := by
      have ht1 := divx x hx
      rcases ht1 with ⟨z,hz⟩
      have ht2: z-x_int = 0 := by
        let dif := z-x_int
        have dif_def: dif = z-x_int := rfl
        rw [← dif_def]
        by_contra! hc
        have hc1: (dif:ℝ) = 0 := by
          rw [dif_def]; simp; rw[hz.left, xinteq]; simp
        have hc2: (dif:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
        contradiction
      have ht3: z = x_int := by
        exact Int.eq_of_sub_eq_zero ht2
      rw [← ht3]
      apply hz.right
    have intxge: x_int ≥ -14 := by
      have ht1: |x_int| ∣ 14 := by
        have: |x_int| = -x_int := by
          exact abs_of_neg intxneg
        rcases intxdiv with ⟨d,hd⟩
        use (-d)
        rw [hd, this]; ring
      have ht2: |x_int| ≤ 14 := by
        rcases ht1 with ⟨d,hd⟩
        have dpos: 0 < d := by
          have tt1: 0 < |x_int| * d := by
            rw [← hd]; norm_num
          have tt2 := abs_nonneg x_int
          exact pos_of_mul_pos_right tt1 tt2
        rw [hd]
        apply le_mul_of_one_le_right (abs_nonneg x_int) dpos
      apply neg_le_of_abs_le ht2
    -- factors of 14 are 1,2,7,14. and if factor is negative, then they are -1,-2,-7,-14.
    have negfactors14: ∀z:ℤ, z ≥ -14 → z ≤ 0 → z ∣ 14 → (z=-1 ∨ z=-2 ∨ z=-7 ∨ z=-14) := by decide
    have intxeq := negfactors14 x_int intxge (le_of_lt intxneg) intxdiv
    rw [xinteq]
    have cast_eq{b:ℤ}: ∀z:ℤ, z = b → (z:ℝ) = b := by
      intro z hz
      exact congrArg Int.cast hz
    rcases intxeq with h1 | h1 | h1 | h1
    <;> rw [cast_eq x_int h1] <;> simp
  -- since x can only be -1,-2,-7,-14, we just substitute in and solve a. then we say that a ≤ 15.
  have aeq: ∀x:ℝ, x^2+a*x=-14 → a=15 ∨ a=9 := by
    intro x hx
    have hhx := xeq x hx
    have cast_back_eq{c d:ℤ}: (c:ℝ) = d → c=d := by
      intro h1
      let dif := c-d
      have dif_def: dif = c-d := rfl
      have h2: (dif:ℝ) = 0 := by
        rw [dif_def]; simp; rw [h1]; simp
      by_contra! hc
      have h3: dif ≠ 0 := by
        rw [dif_def]
        exact sub_ne_zero_of_ne hc
      have h4: (dif:ℝ) ≠ 0 := by
        exact Int.cast_ne_zero.mpr h3
      contradiction
    rcases hhx with xe | xe | xe | xe
    <;> rw [xe] at hx; simp at hx
    · left
      have this: (a:ℝ) = 15 := by
        have: (a:ℝ) = a + -14 + 14 := by ring
        rw [this, ← hx]; ring
      apply cast_back_eq this
    · right
      have: (a:ℝ) = 9 := by
        have: (a:ℝ) = a + (-14/2) + 7 := by ring
        rw [this, ← hx]; ring
      apply cast_back_eq this
    · right
      have: (a:ℝ) = 9 := by
        have: (a:ℝ) = a + (-14/7) + 2 := by ring
        rw [this, ← hx]; ring
      apply cast_back_eq this
    · left
      have: (a:ℝ) = 15 := by
        have: (a:ℝ) = a + (-14/14) + 1 := by ring
        rw [this, ← hx]; ring
      apply cast_back_eq this
  -- a=15 or 9, so a ≤ 15
  by_cases ha15: a = 15; omega
  by_cases ha9: a = 9; omega
  -- if a is not 15 or 9, we can find a contradiction.
  by_contra! agt
  have naeq: ¬ (∀x:ℝ, (x^2+a*x=-14 → a=15 ∨ a=9)) := by
    push_neg
    have h1: ∃x:ℝ, x^2+a*x = -14 := by
      -- the equation is x^2+ax+14=0
      have ht1: ∃s:ℝ, discrim (1:ℝ) (a:ℝ) 14 = s*s := by
        have tt1: discrim (1:ℝ) (a:ℝ) 14 = a^2-56 := by
          rw [discrim]; simp; norm_num
        use √(a^2-56)
        have tt2: 0 ≤ (a^2:ℝ) - 56 :=
        calc
          (0:ℝ) = a^2 - a^2 := by ring
          _ ≤ a^2 - 15^2 := by
            have ht1: (a:ℝ) > 15 := by
              have hh1: a-15 > 0 := by linarith [agt]
              have hh2: a-15 > (0:ℝ) := by
                let dif := a-15
                have dif_def: dif = a-15 := rfl
                rw [← dif_def] at hh1
                have: dif > (0:ℝ) := by
                  simp [hh1]
                rw [dif_def] at this; simp at this
                linarith [this]
              linarith [hh2]
            have ht2: 0 ≤ (15:ℝ) := by norm_num
            have ht3: (a^2:ℝ) ≥ 15^2 := by
              rw [pow_two, pow_two]
              have hh1: (a:ℝ) ≥ 15 := le_of_lt ht1
              exact mul_self_le_mul_self ht2 hh1
            linarith [ht3]
          _ = a^2 - 225 := by ring
          _ ≤ a^2 - 56 := by linarith [norm_num]
        rw [tt1]; symm
        exact Real.mul_self_sqrt tt2
      have ht2: (1:ℝ) ≠ 0 := by norm_num
      have ht3 := exists_quadratic_eq_zero ht2 ht1
      rcases ht3 with ⟨x0,hx0⟩
      use x0
      rw [← add_zero (-14), ← hx0]; ring
    rcases h1 with ⟨x0,hx0⟩
    use x0
  contradiction