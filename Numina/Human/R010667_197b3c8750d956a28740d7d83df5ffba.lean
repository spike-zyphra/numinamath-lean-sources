import Mathlib

/- Prove that for every irrational real number $a$,
there are irrational real numbers $b$ and $b^{\prime}$ so that
$a+b$ and $a b^{\prime}$ are both rational while $a b$ and $a+b^{\prime}$ are both irrational. -/
theorem number_theory_260545 (a : ℝ) (ha : Irrational a) :
    ∃ b b' : ℝ, Irrational b ∧ Irrational b' ∧
      ¬ Irrational (a + b) ∧ ¬ Irrational (a * b') ∧
      Irrational (a * b) ∧  Irrational (a + b') := by
  -- if b-c is irrational, then b irr or c irr
  have irr_sub{b c: ℝ}(h: Irrational (b - c)):
    Irrational b ∨ Irrational c := by
    have: b - c = b + (-c) := by ring
    rw [this] at h
    replace := Irrational.add_cases h
    simp only [irrational_neg_iff] at this
    exact this
  -- notice that a + 1/a, a+2/a, at least one of them is irrational.
  have irr_cases: Irrational (a + 1/a) ∨ Irrational (a + 2/a) := by
    -- it is because a + 2/a - (a + 1/a) = 1/a, irrational.
    have: Irrational (a + 2/a - (a + 1/a)) := by
      have h1: (a + 2/a) - (a + 1/a) = ↑(1:ℚ)/a := by ring
      rw [h1]
      refine Irrational.rat_div ha (by norm_num)
    apply (irr_sub this).symm
  -- therefore exist such b', ab' rational and a+b' irrational
  have exb': ∃b', Irrational b' ∧ ¬ Irrational (a*b') ∧
    Irrational (a + b') := by
    -- it depends on whether 1/a or 2/a is irrational.
    rcases irr_cases with h1 | h2
    · use ((1:ℚ)/a)
      refine ⟨Irrational.rat_div ha (by norm_num), ?_, ?_⟩
      all_goals simp only [Rat.cast_one, h1,
      mul_one_div_cancel ha.ne_zero, not_irrational_one, not_false_eq_true]
    · use ((2:ℚ)/a)
      refine ⟨Irrational.rat_div ha (by norm_num), ?_, ?_⟩
      all_goals simp only [Rat.cast_ofNat, h2,
      mul_div_cancel₀ _ ha.ne_zero, not_irrational_ofNat, not_false_eq_true]
  -- consider whether a^2 irrational.
  by_cases hasq: Irrational (a^2)
  · -- if a^2 is irrational, let b = -a.
    use (-a)
    -- clearly, a+b = 0 rational and ab = -a^2 irrational
    have: Irrational (a* -a) := by
      simp only [mul_neg, irrational_neg_iff,
      ← pow_two, hasq]
    simp only [add_neg_cancel, this, not_irrational_zero,
    true_and, not_false_eq_true, irrational_neg_iff, ha]
    exact exb'
  · -- if a^2 is rational, use a^2-a.
    use (a^2-a)
    have: Irrational (a^2-a) := by
      have: a = a^2 - (a^2-a) := by ring
      rw [this] at ha
      replace := irr_sub ha
      simp only [hasq, false_or] at this
      exact this
    -- clearly, a^2-a+a = a^2 is rational, a^2 - a is irrational.
    simp only [this, add_sub_cancel, hasq, not_false_eq_true, true_and]
    -- a (a^2-a) is irrational, because a = (a(a^2-a) / a^2) + 1
    have h1: a = (a*(a^2-a) / a^2) + ↑(1:ℚ) := by
      field_simp [ha.ne_zero]
      ring
    -- if r + 1 irrational, then r is irrational.
    have h2: Irrational (a*(a^2-a)  / a^2) := by
      rw [h1, irrational_add_rat_iff] at ha
      exact ha
    -- a^2 is rational, the whole fraction is irrational
    -- then numerator must be rational
    have h3 := Irrational.div_cases h2
    simp only [hasq, or_false] at h3
    simp only [h3, true_and]
    exact exb'