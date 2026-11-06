import Mathlib

/- Find $x$ if
\[3 \arctan \frac{1}{4} + \arctan \frac{1}{20} + \arctan \frac{1}{x} = \frac{\pi}{4}.\] -/
theorem calculus_13104 (x : ℝ) (hx : x ≠ 0) :
    3 * Real.arctan (1 / 4) + Real.arctan (1 / 20) + Real.arctan (1 / x) = Real.pi / 4 ↔
    x = 1985 := by
  -- notice that arctan 1/4 can be expressed as argument of 4+i. arctan 1/20, arctan 1/x also follows. so we have the following lemma.
  have lemma_arctan_arg(y:ℝ): 1 < y → Real.arctan (1/y) = (y+Complex.I).arg := by
    intro hy
    have h1: (y+Complex.I).im = 1 := by simp
    have h2: (y+Complex.I).re = y := by simp
    have h3: Real.tan ((y+Complex.I).arg) = 1/y := by
      nth_rw 2 [← h2]
      rw [← h1]
      apply Complex.tan_arg (y+Complex.I)
    rw [← h3]
    apply Real.arctan_tan
    · apply Complex.neg_pi_div_two_lt_arg_iff.mpr
      simp [h1, h2]
    · apply Complex.arg_lt_pi_div_two_iff.mpr
      left; simp; linarith [hy]
  -- when x is positive, arctan x is also positive.
  have lemma_arctan_pos (x:ℝ) (hx: 0 < x):
    0 < Real.arctan x := by
    have ht1: 0 = Real.arctan 0 := Real.arctan_zero.symm
    rw [ht1]
    apply Real.arctan_strictMono hx
  -- then find sum of those arctan, is to find arg of those complex number products.
  have h1: 3 * Real.arctan (1/4) = ((4 + Complex.I)^3).arg := by
    rw [lemma_arctan_arg 4 (by norm_num)]
    have ht1: 3 * (4 + Complex.I).arg = (4 + Complex.I).arg +
      (4 + Complex.I).arg + (4 + Complex.I).arg := by ring
    simp; rw [ht1]
    have ht2: (4 + Complex.I) ≠ 0 := by
      have: (4 + Complex.I).re ≠ 0 := by simp
      symm
      exact ne_of_apply_ne Complex.re fun a => this (id (Eq.symm a))
    have ht3: (4 + Complex.I).arg ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2)
      := by
      simp; constructor
      · apply Complex.neg_pi_div_two_lt_arg_iff.mpr
        simp
      · apply Complex.arg_lt_pi_div_two_iff.mpr
        simp
    have ht4: (4 + Complex.I).arg + (4 + Complex.I).arg ∈
      Set.Ioc (-Real.pi) Real.pi := by
      simp; simp at ht3
      constructor <;> linarith [ht3]
    rw [← Complex.arg_mul ht2 ht2 ht4]
    have ht5: (4+Complex.I)*(4+Complex.I) = 15 + 8*Complex.I := by
      have tt1: (15:ℂ) = 16 + -1 := by ring
      have tt2: (-1:ℂ) = Complex.I * Complex.I := Complex.I_mul_I.symm
      rw [tt1, tt2]; ring
    have ht6: (4+Complex.I)*(4+Complex.I) ≠ 0 := by
      rw [ht5]
      have: (15 + 8*Complex.I).re ≠ 0 := by simp
      symm
      exact ne_of_apply_ne Complex.re fun a => this (id (Eq.symm a))
    have ht7: ((4+Complex.I)*(4+Complex.I)).arg ∈
      Set.Ioo (-(Real.pi/2)) (Real.pi/2) := by
      simp; rw [ht5]; constructor
      · apply Complex.neg_pi_div_two_lt_arg_iff.mpr
        simp
      · apply Complex.arg_lt_pi_div_two_iff.mpr
        simp
    have ht8: ((4+Complex.I)*(4+Complex.I)).arg + (4+Complex.I).arg ∈
      Set.Ioc (-Real.pi) Real.pi := by
      simp; simp at ht3 ht7
      constructor <;> linarith [ht3, ht7]
    rw [← Complex.arg_mul ht6 ht2 ht8]
    rw [pow_three, mul_comm]
  -- we will go step by step here. because arg_mul asks us to verify arguments is between -π and π.
  have h2: (4+Complex.I)^3 = 52 + 47 * Complex.I := by
    have ht1: (4+Complex.I)^2 = 15 + 8*Complex.I := by
      have: (15:ℂ) = 16 + -1 := by ring
      rw [this, ← Complex.I_mul_I]; ring
    rw [pow_three, ← pow_two, ht1]
    have: (52:ℂ) = 60 + 8*-1 := by ring
    rw [this, ← Complex.I_mul_I]; ring
  have h3: 3 * Real.arctan (1/4) + Real.arctan (1/20) =
    ((4 + Complex.I)^3 * (20 + Complex.I)).arg := by
    have ht1: (1:ℝ) < 20 := by norm_num
    rw [h1, lemma_arctan_arg 20 ht1]
    symm
    apply Complex.arg_mul
    · rw [h2]
      have: (52+47*Complex.I).re ≠ 0 := by simp
      symm
      exact ne_of_apply_ne Complex.re fun a => this (id (Eq.symm a))
    · have: (20+Complex.I).re ≠ 0 := by simp
      symm
      exact ne_of_apply_ne Complex.re fun a => this (id (Eq.symm a))
    · rw [h2]
      have hh1: (52 + 47*Complex.I).arg ∈
        Set.Ioo (-(Real.pi/2)) (Real.pi/2) := by
        simp; constructor
        · apply Complex.neg_pi_div_two_lt_arg_iff.mpr
          simp
        · apply Complex.arg_lt_pi_div_two_iff.mpr
          simp
      have hh2: (20 + Complex.I).arg ∈
        Set.Ioo (-(Real.pi/2)) (Real.pi/2) := by
        simp; constructor
        · apply Complex.neg_pi_div_two_lt_arg_iff.mpr
          simp
        · apply Complex.arg_lt_pi_div_two_iff.mpr
          simp
      simp at hh1 hh2; simp
      constructor <;> linarith [hh1, hh2]
  -- combine the two terms. some calculation
  have h4: (4 + Complex.I)^3 * (20 + Complex.I) =
    993 + 992*Complex.I := by
    rw [h2]
    -- 52x20 = 1040
    have: (993:ℂ) =  1040 + 47*-1 := by norm_num
    rw [this, ← Complex.I_mul_I]; ring
  -- argument of 1+i is π/4
  have lemma_arg_four: Real.pi/4 = (1 + Complex.I).arg := by
    have: Complex.abs (1 + Complex.I) = √2 := by
      rw [Complex.abs]; simp
      have: Complex.normSq (1 + Complex.I) = 2 := by
        rw [Complex.normSq]; simp; ring
      simp [this]
    rw [Complex.arg]; simp [this]
    have ht1: (√2)⁻¹ = Real.sin (Real.pi/4) := by
      symm
      rw [Real.sin_pi_div_four]
      field_simp
    rw [ht1]
    symm
    apply Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  -- following is important, because we want 0 < arctan(1/x) < π/4
  have h5: (993 + 992*Complex.I).arg < Real.pi/4 := by
    have ht3: 992 < (√2/2) * Complex.abs (993+992*Complex.I) := by
      have tt1: 992^2 + 992^2 < Complex.normSq (993+992*Complex.I) := by
        rw [Complex.normSq]; simp; linarith
      have tt2: (992*√2)^2 = 992^2+992^2 := by
        ring_nf; field_simp; ring
      rw [Complex.abs]; simp
      have tt3: 992*√2 < √(Complex.normSq (993 + 992 * Complex.I)) := by
        rw [← tt2] at tt1
        exact Real.lt_sqrt_of_sq_lt tt1
      have tt4: 992 < √(Complex.normSq (993 + 992 * Complex.I)) / √2 := by
        have: 0 < √2 := by norm_num
        -- lt_div_iff is deprecated in the new lean4 version, and should use lt_div_iff₀ instead.
        exact (lt_div_iff this).mpr tt3
      have tt5: √(Complex.normSq (993 + 992 * Complex.I)) / √2 =
        √2/2 * √(Complex.normSq (993 + 992 * Complex.I)) := by
        field_simp; ring_nf; field_simp
      rw [← tt5]; exact tt4
    rw [Complex.arg]; simp
    have ht4: Real.pi/4 = Real.arcsin (√2/2) := by
      have: √2/2 = Real.sin (Real.pi/4) := by
        symm
        exact Real.sin_pi_div_four
      rw [this]
      symm
      apply Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    rw [ht4]
    have hh1: √2/2 < 1 := by
      have: √2 < 2 := by
        have hh1: 0 < (2:ℝ) := by norm_num
        have hh2: (2:ℝ) < 2^2 := by norm_num
        exact (Real.sqrt_lt' hh1).mpr hh2
      linarith [this]
    have hh2: 0 < √2/2 := by
      have: 0 < √2 := by norm_num
      linarith [this]
    have hh3: 0 ≤ Complex.abs (993 + 992 * Complex.I) := by
        exact AbsoluteValue.nonneg Complex.abs (993 + 992 * Complex.I)
    have hh4: 0 < Complex.abs (993 + 992 * Complex.I) := by
      by_contra! hc
      have: Complex.abs (993 + 992 * Complex.I) = 0 := le_antisymm hc hh3
      rw [this] at ht3; simp at ht3
      norm_num at ht3
    apply Real.strictMonoOn_arcsin
    · simp
      have hh5: 0 < (992:ℝ) := by norm_num
      constructor
      · have: 0 ≤ 992 / Complex.abs (993 + 992 * Complex.I) := by
          apply div_nonneg (le_of_lt hh5) hh3
        linarith [this]
      · have: 992 / Complex.abs (993 + 992 * Complex.I) < √2/2 := by
          -- div_lt_iff has been deprecated. we should use div_lt_iff₀ instead.
          apply (div_lt_iff hh4).mpr ht3
        linarith [this]
    · simp; constructor <;> linarith [hh1, hh2]
    -- same, should use div_lt_iff₀ here.
    · exact (div_lt_iff hh4).mpr ht3
  -- now we start solving the problem.
  constructor <;> intro h
  -- given the equation, find value of x.
  · have h6 := lemma_arctan_pos (1/4) (by norm_num)
    have h7 := lemma_arctan_pos (1/20) (by norm_num)
    have xpos: 0 < x := by
      have ht1: 0 < Real.arctan (1/x) := by
        have: Real.arctan (1/x) = Real.pi/4 -
          (3*Real.arctan (1/4) + Real.arctan (1/20)) := by
          rw [← h]; ring
        rw [this, h3, h4]; linarith [h5]
      have ht2: 0 < 1/x := by
        have hh1: 0 = Real.arctan 0 := by
          exact Eq.symm Real.arctan_zero
        rw [hh1] at ht1
        by_contra! hc
        have hhc: 1/x < 0 := by
          by_contra! cc
          have: 1/x = 0 := le_antisymm hc cc
          rw [this] at ht1; simp at ht1
        have nht1 := Real.arctan_strictMono hhc
        linarith [ht1, nht1]
      exact one_div_pos.mp ht2
    have h8: 1 < x := by
      have ht1: Real.arctan (1/x) < Real.pi /4 := by
        have: Real.arctan (1/x) = Real.pi/4 -
          (3*Real.arctan (1/4) + Real.arctan (1/20)) := by
          rw [← h]; ring
        rw [this]
        linarith
      have ht2: Real.pi / 4 = Real.arctan 1 := by
        exact Eq.symm Real.arctan_one
      rw [ht2] at ht1
      have ht3: 1/x < 1 := by
        by_contra! hc
        by_cases hh: 1/x = 1
        rw [hh] at ht1; simp at ht1
        have hc': 1 < 1/x := by
          exact lt_of_le_of_ne hc fun a => hh (id (Eq.symm a))
        have ht3 := Real.arctan_strictMono hc'
        linarith [ht1, ht3]
      exact (div_lt_one xpos).mp ht3
    have h9 := lemma_arctan_arg x h8
    have h10: (993+992*Complex.I).arg + (x+Complex.I).arg =
      ((993+992*Complex.I)*(x+Complex.I)).arg := by
      symm
      apply Complex.arg_mul
      · have: (993+992*Complex.I).re ≠ 0 := by simp
        exact Ne.symm (ne_of_apply_ne Complex.re fun a => this (id (Eq.symm a)))
      · have: (x+Complex.I).im ≠ 0 := by simp
        symm
        exact ne_of_apply_ne Complex.im fun a => this (id (Eq.symm a))
      · rw [← h4, ← h3, ← h9, h]; simp;
        constructor <;> linarith [Real.pi_pos]
    have h11: (993+992*Complex.I)*(x+Complex.I) =
      (993*x-992) + (993+992*x)*Complex.I := by
      have: (993*x:ℂ) - 992 = 993*x + 992*-1 := by ring
      rw [this, ← Complex.I_mul_I]; ring
    rw [h3, h4, lemma_arg_four, h9, h10, h11] at h
    -- the equation turns out to be ((993x-992)+(993+992x)i).arg = (1+i).arg
    have h12: (993*x-992) + (993+992*x)*Complex.I ≠ 0 := by
      have: ((993*x-992) + (993+992*x)*Complex.I).im ≠ 0 := by
        simp; linarith
      symm
      exact ne_of_apply_ne Complex.im fun a => this (id (Eq.symm a))
    have h13: 1 + Complex.I ≠ 0 := by
      have: (1+Complex.I).re ≠ 0 := by simp
      exact Ne.symm (ne_of_apply_ne Complex.re fun a => this (id (Eq.symm a)))
    -- next, we work on heq. since the argument equal, real part / imaginary part is equal.
    have heq := (Complex.arg_eq_arg_iff h12 h13).mp h
    let s1 := Complex.abs (1+Complex.I)
    have s1_def: s1 = Complex.abs (1+Complex.I) := rfl
    let s2 := Complex.abs (993 * ↑x - 992 + (993 + 992 * ↑x) * Complex.I)
    have s2_def: s2 = Complex.abs (993 * ↑x - 992 + (993 + 992 * ↑x) * Complex.I) := rfl
    rw [← s1_def, ← s2_def] at heq
    let s3 := s1/s2
    have s3_def: s3 = s1/s2 := rfl
    have s3_def': s3 = (s1:ℂ)/(s2:ℂ) := by
      rw [s3_def]; simp
    rw [← s3_def'] at heq
    have eq: 993*x-992 = 993+992*x := by
      have ht1: ↑s3 * (993 * ↑x - 992 + (993 + 992 * ↑x) * Complex.I) =
        (s3*(993*x-992))+(s3*(993+992*x))*Complex.I := by ring
      let ii := (s3*(993*x-992))+(s3*(993+992*x))*Complex.I
      have ii_def: ii = (s3*(993*x-992))+(s3*(993+992*x))*Complex.I := rfl
      rw [ht1, ← ii_def] at heq
      have ht2: ii.re = 1 := by
        rw [heq]; simp
      have ht3: ii.im = 1 := by
        rw [heq]; simp
      have ht4: ii.re = ii.im := by
        rw [ht2, ht3]
      have ht5: ii.re = s3*(993*x-992) := by
        rw [ii_def]; simp
      have ht6: ii.im = s3*(993+992*x) := by
        rw [ii_def]; simp
      rw [ht5, ht6] at ht4
      have ht7: s3 ≠ 0 := by
        rw [s3_def]
        have hs1: s1 ≠ 0 := by
          rw [s1_def]
          rw [Complex.abs]; simp; rw [Complex.normSq]; simp
        have hs2: s2 ≠ 0 := by
          rw [s2_def]
          rw [Complex.abs]; simp; rw [Complex.normSq]; simp
          have hh1 := sq_nonneg (993 * x - 992)
          have hh2 := sq_nonneg (993 + 992 * x)
          have tt1: 0 ≤ (993 * x - 992) * (993 * x - 992) + (993 + 992 * x) * (993 + 992 * x) := by
            rw [← pow_two, ← pow_two]
            linarith [hh1, hh2]
          have tt2: (993*x-992)*(993*x-992) + (993+992*x)*(993+992*x) ≠ 0 := by
            rw [← pow_two, ← pow_two]
            by_contra! hc
            have hh3: (993*x-992) = 0 := by
              have htt1: (993*x-992)^2 = 0 := by linarith [hh1,hh2,hc]
              rw [pow_two] at htt1
              have htt2 := mul_eq_zero.mp htt1
              tauto
            have hh4: (993+992*x) = 0 := by
              have htt1: (993+992*x)^2 = 0 := by linarith [hh1,hh2,hc]
              rw [pow_two] at htt1
              have htt2 := mul_eq_zero.mp htt1
              tauto
            have hh5: 993*x = 993 * (993+992*x-993)/992 := by ring
            rw [hh5, hh4] at hh3; simp at hh3; norm_num at hh3
          apply (Real.sqrt_ne_zero tt1).mpr tt2
        linarith [hs1, hs2]
      have ht8:993*x-992 = s3*(993*x-992) / s3 := by field_simp [ht7]
      rw [ht8, ht4]; field_simp
    -- solve eq, then x is determined.
    have hh1: x = 993*x-992 - 992*x + 992 := by ring
    rw [hh1, eq]; ring
  -- this direction, we verify x=1985 is the correct solution.
  · have h6 := lemma_arctan_arg 1985 (by norm_num)
    have h7: (993+992*Complex.I).arg + (1985+Complex.I).arg =
      ((993+992*Complex.I)*(1985+Complex.I)).arg := by
      symm
      apply Complex.arg_mul
      · have: (993+992*Complex.I).re ≠ 0 := by simp
        exact Ne.symm (ne_of_apply_ne Complex.re fun a => this (id (Eq.symm a)))
      · have: (1985+Complex.I).re ≠ 0 := by simp
        exact Ne.symm (ne_of_apply_ne Complex.re fun a => this (id (Eq.symm a)))
      · push_cast at h6
        have hh1: (993 + 992*Complex.I).arg ∈
        Set.Ioo (-(Real.pi/2)) (Real.pi/2) := by
          simp; constructor
          · apply Complex.neg_pi_div_two_lt_arg_iff.mpr
            simp
          · apply Complex.arg_lt_pi_div_two_iff.mpr
            simp
        have hh2: (1985+ Complex.I).arg ∈
        Set.Ioo (-(Real.pi/2)) (Real.pi/2) := by
          simp; constructor
          · apply Complex.neg_pi_div_two_lt_arg_iff.mpr
            simp
          · apply Complex.arg_lt_pi_div_two_iff.mpr
            simp
        simp at hh1 hh2
        simp; constructor <;> linarith [hh1, hh2]
    have h8: (993+992*Complex.I)*(1985+Complex.I) =
      (993*1985-992) + (992*1985+993)*Complex.I := by
      have: (992:ℂ) = - 992*-1 := by ring
      nth_rw 2 [this]
      rw [← Complex.I_mul_I]; ring
    rw [h3, h4, h, h6]; push_cast; rw [h7, h8]
    norm_num
    -- now the goal turns to be show argument of (1970113+1970113i) is π/4
    rw [Complex.arg]; simp
    rw [Complex.abs]; simp
    rw [Complex.normSq]; simp;
    have h9: 1970113 / √(1970113 * 1970113 + 1970113 * 1970113) =
      √2/2 := by
      have ht1: 1970113 * 1970113 + 1970113 * 1970113 =
        (√2*1970113)^2 := by
        have: √2^2 = 2 := by field_simp
        ring_nf; simp [this]; ring
      have ht2: √((√2*1970113)^2) = (√2*1970113) := by
        have: 0 ≤ √2*1970113 := by norm_num
        exact Real.sqrt_sq this
      rw [ht1, ht2]
      field_simp; ring_nf; field_simp; ring
    have h10: Real.sin (Real.pi/4) = √2/2 := by
      exact Real.sin_pi_div_four
    rw [h9, ← h10]
    apply Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])