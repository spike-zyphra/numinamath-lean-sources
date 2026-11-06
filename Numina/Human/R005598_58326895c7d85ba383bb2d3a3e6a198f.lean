import Mathlib

/- Find the sum of all real solutions for $x$ to the equation
$\left(x^{2}+2 x+3\right)^{\left(x^{2}+2 x+3\right)^{\left(x^{2}+2 x+3\right)}}=2012$. -/
theorem algebra_609063:
  ∑ᶠ x ∈ {x:ℝ | (x^2+2*x+3)^(x^2+2*x+3)^(x^2+2*x+3) = 2012}, x = -2 := by
  -- function y^y^y is strictly increasing
  have hinc{y1 y2: ℝ}(h: y1 > y2)(hy2: y2 > 1): y1^y1^y1 > y2^y2^y2 := by
    -- y1^y1 > y2^y2
    have h1: y1^y1 > y2^y2 := by
      have: y1^y1 > y1^y2 := by
        apply Real.rpow_lt_rpow_of_exponent_lt ?_ h
        apply hy2.trans h
      apply lt_trans ?_ this
      apply Real.rpow_lt_rpow ?_ h ?_
      all_goals linarith [hy2]
    -- y1^y1^y1 > y1^y2^y2
    have h2: y1^y1^y1 > y1^y2^y2 := by
      apply Real.rpow_lt_rpow_of_exponent_lt ?_ h1
      apply hy2.trans h
    apply lt_trans ?_ h2
    apply Real.rpow_lt_rpow ?_ h ?_
    · linarith [hy2]
    · apply Real.rpow_pos_of_pos (by linarith [hy2])
  -- from strict monotone, y^y^y is injective
  have hinj{y1 y2:ℝ}(hy1: y1 > 1)(hy2: y2 > 1)
    (heq: y1^y1^y1 = y2^y2^y2): y1 = y2 := by
    by_contra!
    replace: y1 < y2 ∨ y2 < y1 := lt_or_gt_of_ne this
    rcases this with y1lty2 | y2lty1
    · have := hinc y1lty2 hy1
      simp [heq] at this
    · have := hinc y2lty1 hy2
      simp [heq] at this
  -- equation y^y^y = 2012 has a solution.
  have: ∃ (y:ℝ), 1 < y ∧ y^y^y = 2012 := by
    set f: ℝ → ℝ := fun x => x^x^x with f_def
    -- such solution exist.
    have: ∃(y:ℝ), 1 < y ∧ f y = 2012 := by
      -- notice that 2^2^2 < 2012 < 3^3^3 and continuous on interval 2,3.
      -- then we can use intermediate theorem.
      have hh1: Set.Icc (f 2) (f 3) ⊆ f '' Set.Icc 2 3 := by
        apply intermediate_value_Icc (by norm_num)
        rw [f_def]
        apply continuousOn_of_forall_continuousAt
        intro x hx
        simp only [Set.mem_Icc] at hx
        apply ContinuousAt.rpow continuousAt_id ?_ ?_
        · apply ContinuousAt.rpow continuousAt_id
            continuousAt_id ?_
          simp only [id_eq]
          right; linarith [hx.left]
        · left; symm; apply ne_of_lt
          simp only [id_eq]; linarith [hx.left]
      have hh2: 2012 ∈ Set.Icc (f 2) (f 3) := by
        rw [f_def]
        simp only [Real.rpow_two, Set.mem_Icc]
        norm_num
      replace hh2: 2012 ∈ f '' Set.Icc 2 3 := hh1 hh2
      rcases hh2 with ⟨y, hy⟩
      use y
      simp only [Set.mem_Icc] at hy
      exact ⟨(by linarith [hy.left]), hy.right⟩
    simp only [f_def] at this
    exact this
  -- suppose y is a solution of y^y^y = 2012
  rcases this with ⟨y, hy⟩
  -- then x^2+2x+3 = y.
  have h1: {x:ℝ | (x^2+2*x+3)^(x^2+2*x+3)^(x^2+2*x+3) = 2012} =
    {x:ℝ | x^2+2*x + (3-y) = 0} := by
    ext x
    constructor <;> intro h
    · simp only [Set.mem_setOf_eq] at h
      -- solution of y^y^y=2012 is unique
      have: x^2+2*x+3 = y := by
        -- x^2+2x+3 ≥ 1
        have h1: x^2+2*x+3 > 1 := by
          have: x^2+2*x+3 = (x+1)^2 + 2 := by ring
          rw [this]
          linarith [sq_nonneg (x+1)]
        -- y^y^y is injective.
        apply hinj h1 hy.left ?_
        rw [hy.right, h]
      simp only [Set.mem_setOf_eq]
      rw [← this]; ring
    · simp only [Set.mem_setOf_eq] at h
      have: x^2+2*x+3 = y := by linarith [h]
      -- y is a solution.
      simp only [Set.mem_setOf_eq, this, hy.right]
  -- easy to show y ≥ 2, since y^y^y is increasing.
  have: y ≥ 2 := by
    by_contra!
    replace: y^y^y ≤ 2^(2:ℝ)^(2:ℝ) := by
      apply le_of_lt
      apply hinc this hy.left
    rw [hy.right] at this
    norm_num at this
  -- then exist s^2 = y-2
  obtain ⟨s, hs⟩: ∃ s, s^2 = y-2 := by
    use √(y-2)
    apply Real.sq_sqrt
    linarith [this]
  -- and s ≠ -s, or s ≠ 0.
  have sne: s ≠ -s := by
    by_contra! h
    -- otherwise y = 2. but 2^2^2 ≠ 2012
    replace h: s = 0 := eq_zero_of_neg_eq h.symm
    replace h: y = 2 := by
      rw [h, zero_pow (by norm_num)] at hs
      linarith [hs]
    rw [h] at hy
    norm_num at hy
  -- x^2+2x+3-y = 0, then (x+1)^2 = y-2 = s^2
  have h2: {x:ℝ | x^2+2*x + (3-y) = 0} = {x:ℝ | x+1 = s ∨ x+1 = -s} := by
    replace: {x:ℝ | x^2+2*x + (3-y) = 0} =
      {x:ℝ | (x+1)^2 = s^2} := by
      ext x
      simp only [Set.mem_setOf_eq, hs]
      constructor <;> intro h
      all_goals nlinarith [h]
    rw [this]; ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      apply eq_or_eq_neg_of_sq_eq_sq _ _ h
    · rintro (h | h)
      all_goals simp [h]
  -- then x = s-1 or -s-1
  have h3: {x:ℝ | x+1 = s ∨ x+1 = -s} = {s-1, -s-1} := by
    ext x
    simp only [Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    all_goals
      rintro (h | h)
      · left; linarith [h]
      · right; linarith [h]
  rw [h1, h2, h3, finsum_mem_pair (by simp [sne])]
  -- s-1 + -s+1 = -2.
  -- in fact, use Vieta's formula, we reach this result immediately.
  ring