import Mathlib

/-- Two real numbers are selected independently and at random from the interval [−20,10].
    What is the probability that the product of those numbers is greater than zero?
   (A) 19(B) 13(C) 49(D) 59(E) 23 -/
theorem algebra_95002 :
    (MeasureTheory.volume {x ∈ Set.Icc (-20 : ℝ) 10 ×ˢ Set.Icc (-20 : ℝ) 10 | x.1 * x.2 > 0})
    / (MeasureTheory.volume (Set.Icc (-20 : ℝ) 10 ×ˢ Set.Icc (-20 : ℝ) 10)) = (5 : ENNReal) / (9 : ENNReal) := by
  -- The area covered by [-20,10]^2 is 900.
  have : MeasureTheory.volume (Set.Icc (-20 : ℝ) 10 ×ˢ Set.Icc (-20 : ℝ) 10) = 900 := by
    rw[MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp only [Real.volume_Icc, sub_neg_eq_add]
    norm_num
  rw[this]
  -- For the product to be positive, both numbers must be positive or both negative.
  -- Call the numbers x,y. This is the case when x and y are both in [-20,0) or both in (0,10].
  have : {x : ℝ × ℝ | x ∈ Set.Icc (-20) 10 ×ˢ Set.Icc (-20) 10 ∧ x.1 * x.2 > 0} =
      (Set.Ico (-20) 0 ×ˢ Set.Ico (-20) 0) ∪ (Set.Ioc 0 10 ×ˢ Set.Ioc 0 10) := by
    ext ⟨a,b⟩
    simp[mul_pos_iff]
    constructor
    · rintro ⟨⟨⟨ha1,hb1⟩,⟨ha2,hb2⟩⟩,(⟨ha3,hb3⟩|⟨ha3,hb3⟩)⟩
      · simp[*]
      · simp[*]
    · rintro (⟨⟨ha1.hb1⟩,⟨ha2,hb2⟩⟩|⟨⟨ha1.hb1⟩,⟨ha2,hb2⟩⟩)
      · simp only [and_self, true_and, or_true, and_true, *]
        split_ands <;> linarith
      · simp only [and_self, and_true, true_or, *]
        split_ands <;> linarith
  rw[this]
  -- Since these sets are disjoint, the area of the union is the sum of the areas.
  rw[MeasureTheory.measure_union]
  · rw[MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    -- But the area of [-20,0) x [-20,0) is 400 and the area of (0,10] x (0,10] is 100.
    simp only [Real.volume_Ico, sub_neg_eq_add, zero_add, ENNReal.ofReal_ofNat,
      MeasureTheory.Measure.prod_prod, Real.volume_Ioc, sub_zero]
    norm_num
    -- So the probability is 500/900 = 5/9.
    convert_to (5 * 100 : ENNReal) / (9 * 100 : ENNReal) = (5 : ENNReal) / (9 : ENNReal) using 2
    · norm_num
    · norm_num
    · rw[ENNReal.mul_div_mul_right 5 (9 : ENNReal)] <;> simp
  · rw[Set.disjoint_iff]
    rintro ⟨a,b⟩ ⟨⟨h1,h2⟩, ⟨h3,h4⟩⟩
    simp at h1 h2 h3 h4
    linarith
  · apply MeasurableSet.prod
    · simp
    · simp