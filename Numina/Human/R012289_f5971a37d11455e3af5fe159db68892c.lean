import Mathlib


/- 1. Find the real number $m$ such that the equation

$$
\left(x^{2}-2 m x-4\left(m^{2}+1\right)\right)\left(x^{2}-4 x-2 m\left(m^{2}+1\right)\right)=0
$$

has exactly three distinct real roots. -/
theorem algebra_223292 {m:ℝ}:
  {x:ℝ | (x^2-2*m*x - 4*(m^2+1)) * (x^2-4*x-2*m*(m^2+1)) = 0}.encard = 3 ↔
  m = 3 := by

  -- it suffices to consider number of roots of the two quadratice equations.
  have: {x:ℝ | (x^2-2*m*x - 4*(m^2+1)) * (x^2-4*x-2*m*(m^2+1)) = 0} =
    {x:ℝ | 1*(x*x) + (-2*m)*x + (-4*(m^2+1)) = 0 ∨
      1*(x*x) + (-4)*x + (-2*m*(m^2+1)) = 0 } := by
    ext x
    simp only [mul_eq_zero, Set.mem_setOf_eq, one_mul, neg_mul]
    ring_nf
  rw [this]

  -- first equation always have two roots.
  have eq1 {x:ℝ}: 1*(x*x) + (-2*m)*x + (-4*(m^2+1)) = 0 ↔
    (x = m+√(5*m^2+4) ∨ x = m - √(5*m^2+4)) := by
    replace: discrim (1:ℝ) (-2*m) (-4*(m^2+1)) =
      (2*√(5*m^2+4)) * (2*√(5*m^2+4)) := by
      nth_rw 2 [mul_comm 2 _]
      rw [← mul_assoc, mul_assoc 2 _ _,
      ← pow_two, Real.sq_sqrt (by linarith only [sq_nonneg m])]
      dsimp only [discrim]
      ring
    rw [quadratic_eq_zero_iff (by norm_num) this]
    ring_nf

  have eq1': {x:ℝ | 1*(x*x) + (-2*m)*x + (-4*(m^2+1)) = 0} =
    {m+√(5*m^2+4), m - √(5*m^2+4)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
    rw [← eq1]


  -- consider discriminant of second equation
  have hdis: discrim (1:ℝ) (-4) (-2*m*(m^2+1)) =
    4*(4+2*m*(m^2+1)) := by
    dsimp only [discrim]
    ring
  replace hdis: discrim (1:ℝ) (-4) (-2*m*(m^2+1)) =
    8 * ((m+1)*( (m-1/2)^2 + 7/4)) := by
    rw [hdis]
    ring

  have pair_card: ({m+√(5*m^2+4), m - √(5*m^2+4)}: Set ℝ).encard = 2 := by
    apply Set.encard_pair
    apply ne_of_gt
    replace: 0 < √(5*m^2+4) := by
      refine Real.sqrt_pos_of_pos ?_
      linarith only [sq_nonneg m]
    linarith only [this]


  constructor
  · intro h

    -- if m < -1, second quadratic equation has no roots.
    -- then the set only contain two elements, contradiction.
    have hm: m ≥ -1 := by
      by_contra! hm
      have h1: discrim 1 (-4) (-2*m*(m^2+1)) < 0 := by
        rw [hdis]
        apply mul_neg_of_pos_of_neg (by norm_num) ?_
        apply mul_neg_of_neg_of_pos ?_ ?_
        <;> linarith only [sq_nonneg (m-1/2), hm]
      have h2: {x:ℝ | 1*(x*x) + (-2*m)*x + (-4*(m^2+1)) = 0 ∨
        1*(x*x) + (-4)*x + (-2*m*(m^2+1)) = 0 } =
        {m+√(5*m^2+4), m - √(5*m^2+4)} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff]
        rw [← eq1]
        simp only [or_iff_left_iff_imp]
        intro hh
        absurd hh
        apply quadratic_ne_zero_of_discrim_ne_sq
        rintro s hs
        rw [hs] at h1
        linarith only [h1, sq_nonneg s]
      rw [h2] at h
      norm_num [h] at pair_card

    -- if m = -1, second equation has one root.
    -- but this root is similar to the first equation, then also contradiction.
    replace hm: m > -1 := by
      apply lt_of_le_of_ne hm ?_
      rintro meq
      have h2: {x:ℝ | 1*(x*x) + (-2*m)*x + (-4*(m^2+1)) = 0 ∨
        1*(x*x) + (-4)*x + (-2*m*(m^2+1)) = 0 } =
        {m+√(5*m^2+4), m - √(5*m^2+4)} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff]
        rw [eq1]
        simp only [or_iff_left_iff_imp]
        intro hh
        replace hdis: discrim 1 (-4) (-2*m*(m^2+1)) = 0 := by
          rw [discrim]
          norm_num [← meq]
        rw [quadratic_eq_zero_iff_of_discrim_eq_zero
        (by norm_num) hdis] at hh
        left
        norm_num [hh, ← meq]
        have: √(9:ℝ) = 3 := by
          have: (9:ℝ) = 3^2 := by norm_num
          rw [this, Real.sqrt_sq (by norm_num)]
        norm_num [this]
      rw [h2] at h
      norm_num [h] at pair_card

    -- when m > -1, discriminant of second equation > 0.
    obtain ⟨s, hs, spos⟩: ∃ s:ℝ, discrim 1 (-4) (-2*m*(m^2+1)) = s*s ∧
      0 < s := by
      have: 0 < discrim 1 (-4) (-2*m*(m^2+1)) := by
        rw [hdis]
        apply mul_pos (by norm_num) ?_
        apply mul_pos ?_ ?_
        <;> linarith only [hm, sq_nonneg (m - 1/2)]
      use √(discrim 1 (-4) (-2*m*(m^2+1)))
      rw [← pow_two, Real.sq_sqrt this.le]
      simp only [Real.sqrt_pos, true_and, this]

    -- it has two roots.
    have eq2: {x:ℝ | 1*(x*x) + (-4)*x + (-2*m*(m^2+1)) = 0} =
      {2+s/2, 2-s/2} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
      rw [quadratic_eq_zero_iff (by norm_num) hs]
      ring_nf
    have eq2': ({2+s/2, 2-s/2}: Set ℝ).encard = 2 := by
      apply Set.encard_pair
      apply ne_of_gt
      linarith only [spos]

    -- we claim the two equations have some common roots,
    -- otherwise the set contain four elements, not three.
    have h1: {x:ℝ | 1*(x*x) + (-2*m)*x + (-4*(m^2+1)) = 0 ∨
        1*(x*x) + (-4)*x + (-2*m*(m^2+1)) = 0 } =
      {x:ℝ | 1*(x*x) + (-2*m)*x + (-4*(m^2+1)) = 0} ∪
      {x:ℝ |  1*(x*x) + (-4)*x + (-2*m*(m^2+1)) = 0 } := rfl
    have h2: ¬ Disjoint {x:ℝ | 1*(x*x) + (-2*m)*x + (-4*(m^2+1)) = 0}
      {x:ℝ |  1*(x*x) + (-4)*x + (-2*m*(m^2+1)) = 0 } := by
      by_contra!
      rw [h1, Set.encard_union_eq this,
      eq2, eq1', pair_card, eq2'] at h
      norm_num at h
    rw [Set.not_disjoint_iff] at h2
    rcases h2 with ⟨x0, hx0⟩
    simp only [one_mul, neg_mul, Set.mem_setOf_eq] at hx0

    -- suppose this common root is x0, we solve x0 = m^2+1
    have x0eq: x0 = m^2 + 1 := by
      have: 2*m*x0 + 4*(m^2+1) = 4*x0 + 2*m*(m^2+1) := by
        linarith only [hx0]
      replace: (2*m-4) * x0 = (2*m-4) * (m^2+1) := by
        linarith only [this]
      -- if m = 2, the set only have two elements, contradiction.
      have mne: 2*m-4 ≠ 0 := by
        by_contra!
        replace: m = 2 := by linarith only [this]
        have seq: s = 4*√6 := by
          have: s^2 = (4*√6)^2 := by
            nth_rw 1 [pow_two, ← hs]
            rw [this, mul_pow, Real.sq_sqrt (by norm_num)]
            dsimp [discrim]
            norm_num [this]
          rwa [sq_eq_sq₀ spos.le (by norm_num)] at this
        have not_h:
          {x:ℝ | 1*(x*x) + (-2*m)*x + (-4*(m^2+1)) = 0 ∨
          1*(x*x) + (-4)*x + (-2*m*(m^2+1)) = 0 }.encard = 2 := by
          rw [h1, eq2, eq1', seq, this]
          norm_num
          have h2: 4*√6/2 = √24 := by
            have: (24:ℝ) = 2^2 * 6 := by norm_num
            rw [this, Real.sqrt_mul (by norm_num),
            Real.sqrt_sq (by norm_num)]
            ring
          have h3: 0 < √24 := by
            apply Real.sqrt_pos_of_pos (by norm_num)
          simp only [h2, Set.mem_insert_iff, Set.mem_singleton_iff,
          or_true, Set.insert_eq_of_mem, true_or]
          apply Set.encard_pair
          apply ne_of_gt (by linarith only [h3])
        rw [not_h] at h
        norm_num at h
      simpa only [mul_eq_mul_left_iff, mne, or_false] using this

    -- substitute this result into first equation, we solve m = 3.
    have h2: (m^2+1) * ((m+1)*(m-3)) = 0 := by
      rw [x0eq] at hx0
      linarith only [hx0.left]
    have h21: 0 < m^2+1 := by linarith only [sq_nonneg m]
    have h22: m+1 ≠ 0 := by
      linarith only [hm]
    simp only [mul_eq_zero, h22, false_or, h21.ne'] at h2
    linarith only [h2]



  · -- when m = 3, easy to verify three roots are -4, 10, -6
    intro hm
    have: {x:ℝ | 1*(x*x) + (-2*m)*x + (-4*(m^2+1)) = 0 ∨
      1*(x*x) + (-4)*x + (-2*m*(m^2+1)) = 0 } =
      ({-6, -4, 10}: Finset ℝ) := by
      ext x
      simp only [one_mul, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff, ← pow_two]
      norm_num [hm]
      constructor
      · rintro (heq | heq)
        · replace heq: (x - 10) * (x + 4) = 0 := by
            rw [← heq]
            ring
          simp only [mul_eq_zero] at heq
          rcases heq with hl | hr
          · right;right; linarith only [hl]
          · right;left; linarith only [hr]
        · replace heq: (x+6) * (x-10) = 0 := by
            rw [← heq]
            ring
          simp only [mul_eq_zero] at heq
          rcases heq with hl | hr
          · left; linarith only [hl]
          · right; right; linarith only [hr]
      · rintro (rfl | rfl | rfl)
        <;> norm_num
    rw [this, Set.encard_coe_eq_coe_finsetCard]
    norm_num