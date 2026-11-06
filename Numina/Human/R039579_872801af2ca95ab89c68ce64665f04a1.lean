import Mathlib

/- Find all triples $(x, y, z)$ of real positive numbers, which satisfy the system
$$
\left\{\begin{array}{l}
\frac{1}{x}+\frac{4}{y}+\frac{9}{z}=3 \\
x+y+z \leq 12
\end{array}\right.
$$-/
theorem algebra_604680{x y z: ℝ}(xpos: 0 < x)
  (ypos: 0 < y)(zpos: 0 < z):
  (1/x+4/y+9/z=3 ∧ x+y+z≤12) ↔ (x=2 ∧ y=4 ∧ z=6) := by
  -- by AM-GM, a+b ≥ 2√ab given a,b > 0
  have lemma_amgm{a b: ℝ}(ha: 0 < a)(hb: 0 < b):
    a+b ≥ 2*√(a*b) := by
    have h1: a = (√a)^2 := by simp [le_of_lt ha]
    have h2: b = (√b)^2 := by simp [le_of_lt hb]
    nth_rw 1 [h1 ,h2]
    apply le_trans ?_ (two_mul_le_add_sq √a √b)
    apply le_of_eq
    simp [mul_assoc, Real.sqrt_mul (le_of_lt ha)]
  have sqrt4: √(4:ℝ) = 2 := by
    refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
    all_goals norm_num
  have sqrt9: √(9:ℝ) = 3 := by
    refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
    all_goals norm_num
  -- equal condition of a+b ≥ 2√ab is a=b
  have lemma_amgm_eq{a b: ℝ}(ha: 0 < a)(hb: 0 < b)
    (heq: a+b = 2*√(a*b)): a=b := by
    have h1: a = (√a)^2 := by simp [le_of_lt ha]
    have h2: b = (√b)^2 := by simp [le_of_lt hb]
    nth_rw 1 [h1 ,h2] at heq
    rw [Real.sqrt_mul (le_of_lt ha)] at heq
    have h3: (√a - √b)^2 = 0 := by
      have: (√a - √b)^2 = √a^2 + √b^2 - 2*(√a*√b) := by ring
      simp [this, heq]
    simp at h3
    rw [h1, h2, eq_of_sub_eq_zero h3]
  -- apply am-gm, following inequalities hold.
  -- 4x/y + y/x ≥ 2 x √4 = 4
  have xy4: 4 = 2*√(4*x/y * (y/x)) := by
    field_simp [xpos, ypos]
    rw [sqrt4]; norm_num
  have ineq4: 4*x/y + y/x ≥ 4 := by
    nth_rw 2 [xy4]
    apply lemma_amgm
    · apply div_pos (by simp [xpos]) ypos
    · apply div_pos ypos xpos
  -- z/x + 9x/z ≥ 2 x √9 = 6
  have zx6: 6 = 2*√(z/x * (9*x/z)) := by
    field_simp [xpos, zpos]
    rw [sqrt9]; ring
  have ineq9: z/x + 9*x/z ≥ 6 := by
    rw [zx6]
    apply lemma_amgm
    · apply div_pos zpos xpos
    · apply div_pos (by simp [xpos]) zpos
  -- 4z/y + 9y/z ≥ 2 x √36 = 12
  have zy12: 12 = 2*√(4*z/y * (9*y/z)) := by
    field_simp [ypos, zpos]
    rw [sqrt4, sqrt9]
    ring
  have ineq49: 4*z/y+9*y/z ≥ 12 := by
    rw [zy12]
    apply lemma_amgm
    all_goals apply div_pos (by simp [ypos, zpos])
    all_goals simp [ypos, zpos]
  -- back to the problem
  constructor; rintro ⟨heq, hineq⟩
  · -- multiply the equation to the inequality
    have h1: (x+y+z)*(1/x+4/y+9/z) ≤ 36 := by
      rw [heq]; linarith [hineq]
    -- simplify
    have h2: (x+y+z) * (1/x + 4/y + 9/z) =
      (4*x/y + y/x) + (z/x+9*x/z) + (4*z/y + 9*y/z)
      + 14 := by
      field_simp [xpos, ypos, zpos]; ring
    -- substitute in, and cancel 14 from both sides
    have h3: (4*x/y+y/x)+(z/x+9*x/z)+(4*z/y+9*y/z) ≤ 22 := by
      rw [h2] at h1; linarith [h1]
    -- but by AM-GM, those three terms ≥ 22
    have h4: (4*x/y+y/x)+(z/x+9*x/z)+(4*z/y+9*y/z) ≥ 22 := by
      -- sum ≥ 4+6+12 = 22
      linarith [ineq4, ineq9, ineq49]
    -- that is to say, those three terms add equal 22
    have addeq := le_antisymm h3 h4
    -- for the whole sum reach minimum (=22), each term must reach minimum.
    have hxy: 4*x/y + y/x = 4 := by
      by_contra!
      replace := lt_of_le_of_ne ineq4 this.symm
      replace: 4*x/y+y/x + (z/x+9*x/z) + (4*z/y+9*y/z) > 22 := by
        linarith [this, ineq9, ineq49]
      simp [addeq] at this
    -- then we solve 4x/y = y/x, or y = 2x
    replace hxy: y = 2*x := by
      have: 4*x/y = y/x := by
        apply lemma_amgm_eq ?_ ?_ ?_
        · apply div_pos (by simp [xpos]) ypos
        · apply div_pos ypos xpos
        · rw [← xy4, hxy]
      field_simp at this
      apply (sq_eq_sq₀ (le_of_lt ypos) ?_).mp ?_
      · simp [le_of_lt xpos]
      · simp [pow_two, ← this]; ring
    -- also,  z/x + 9x/z = 6
    have hzx: z/x + 9*x/z = 6 := by
      by_contra!
      replace := lt_of_le_of_ne ineq9 this.symm
      replace: 4*x/y+y/x + (z/x+9*x/z) + (4*z/y+9*y/z) > 22 := by
        linarith [this, ineq9, ineq49]
      simp [addeq] at this
    -- we solve z=3x
    replace hzx: z = 3*x := by
      have: z/x = 9*x/z := by
        apply lemma_amgm_eq ?_ ?_ ?_
        · apply div_pos zpos xpos
        · apply div_pos (by simp [xpos]) zpos
        · rw [← zx6, hzx]
      field_simp at this
      apply (sq_eq_sq₀ (le_of_lt zpos) ?_).mp ?_
      · simp [le_of_lt xpos]
      · simp [pow_two, this]; ring
    -- substitute these terms into 1/x + 4/y + 9/z = 3, and solve x,y,z.
    have xeq: x = 2 := by
      simp [hxy, hzx] at heq
      field_simp [xpos] at heq
      ring_nf at heq
      have: x * (x-2) = 0 := by
        have: x*(x-2) = (x^2*18-x*36)/18 := by
          field_simp; ring
        simp [this, heq]
      rcases (mul_eq_zero.mp this) with hx | hx
      · simp [hx] at xpos
      · rw [← add_zero 2, ← hx]; simp
    have yeq: y = 4 := by
      simp [hxy, xeq]; norm_num
    have zeq: z = 6 := by
      simp [hzx, xeq]; norm_num
    -- done.
    exact ⟨xeq, yeq, zeq⟩
  · -- this direction, we verify given x,y,z satisfy the condition. easy.
    rintro ⟨xeq, yeq, zeq⟩
    simp [xeq, yeq, zeq]
    norm_num