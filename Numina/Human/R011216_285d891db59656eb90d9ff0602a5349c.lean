import Mathlib

/- How many real numbers $x$ are solutions to the following equation?

$$
2003^{x}+2004^{x}=2005^{x}
$$ -/
theorem algebra_611305:
  {x:ℝ | (2003:ℝ)^x + 2004^x = 2005^x}.encard = 1 := by
  -- the equation is equivalent to (2003/2005)^x + (2004/2005)^x = 1.
  have h1(x:ℝ)(heq: ((2003:ℝ)/2005)^x + (2004/2005)^x = 1):
    (2003:ℝ)^x + 2004^x = 2005^x := by
    rw [Real.div_rpow, Real.div_rpow] at heq
    field_simp at heq
    exact heq
    all_goals norm_num
  have h1'(x:ℝ)(heq: (2003:ℝ)^x + 2004^x = 2005^x):
    ((2003:ℝ)/2005)^x + (2004/2005)^x = 1 := by
    rw [Real.div_rpow, Real.div_rpow]
    field_simp
    rw [heq]
    all_goals norm_num
  -- it's of the form a^x + b^x = 1.
  -- it suffices to prove a^x+b^x can reach 1, and it's injective.
  -- given 0 < a,b < 1, a^x + b^x = 1 has solution.
  have h2{a b: ℝ}(ha: 0 < a ∧ a < 1)(hb: 0 < b ∧ b < 1):
    ∃ x:ℝ, a^x+b^x = 1 := by
    have hh1: a^(0:ℝ) + b^(0:ℝ) ≥ 1 := by simp
    -- given a,b < 1, for very large n, a^x, b^x tends to 0.
    -- therefore add < 1 for some large n.
    have hh2{c:ℝ}(hc: 0 < c ∧ c < 1): ∃x:ℝ, c^x < 1/2 := by
      have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
        (le_of_lt hc.left) hc.right
      rw [tendsto_atTop_nhds] at hh
      specialize hh ({x:ℝ | -1/2 < x ∧ x < 1/2})
      simp only [Set.mem_setOf_eq, inv_pos, Nat.ofNat_pos, and_true] at hh
      norm_num at hh
      have: IsOpen {x:ℝ | -(1/2) < x ∧ x < 1/2} := by
        refine IsOpen.and ?_ ?_
        · exact isOpen_lt' (-(1 / 2))
        · exact isOpen_gt' (1 / 2)
      rcases (hh this) with ⟨X, hX⟩
      use X
      specialize hX X le_rfl
      rw [Real.rpow_natCast]
      exact hX.right
    -- then exist x, such that a^x + b^x < 1/2 + 1/2 = 1
    rcases (hh2 ha) with ⟨x1, hx1⟩
    rcases (hh2 hb) with ⟨x2, hx2⟩
    have hh3: a^(max x1 x2) + b^(max x1 x2) ≤ 1 := by
      have hh3: a^(max x1 x2) ≤ a^x1 := by
        rw [Real.rpow_le_rpow_left_iff_of_base_lt_one ha.left ha.right]
        exact le_max_left x1 x2
      have hh4: b^(max x1 x2) ≤ b^x2 := by
        apply (Real.rpow_le_rpow_left_iff_of_base_lt_one hb.left hb.right).mpr
        apply le_max_right
      linarith [hx1, hx2, hh3, hh4]
    -- since a^x, b^x are continuous,
    -- by intermediate theorem, a^x+b^x=1 has solution.
    apply intermediate_value_univ₂ ?_ ?_ hh3 hh1
    · have hh1: Continuous fun (x:ℝ) => a^x := by
        rw [continuous_iff_continuousAt]
        intro c
        apply Real.continuousAt_const_rpow ha.left.ne'
      have hh2: Continuous fun (x:ℝ) => b^x := by
        rw [continuous_iff_continuousAt]
        intro c
        apply Real.continuousAt_const_rpow hb.left.ne'
      apply Continuous.add hh1 hh2
    · continuity
  rw [Set.encard_eq_one]
  -- next, we show such solution is unique.
  have h3{a b x y: ℝ}(ha: 0 < a ∧ a < 1)(hb: 0 < b ∧ b < 1)
    (hx: a^x + b^x = 1)(hy: a^y + b^y = 1):
    x = y := by
    -- a^x, b^x is injective, so a^x+b^x also injective.
    rcases (lt_trichotomy x y) with xlty | xeqy | yltx
    · have hh1: a^y < a^x := (Real.rpow_lt_rpow_left_iff_of_base_lt_one
        ha.left ha.right).mpr xlty
      have hh2: b^y < b^x := (Real.rpow_lt_rpow_left_iff_of_base_lt_one
        hb.left hb.right).mpr xlty
      have hh3: (1:ℝ) < 1 := by
        nth_rw 1 [← hy, ← hx]
        linarith [hh1, hh2]
      norm_num at hh3
    · exact xeqy
    · have hh1: a^x < a^y := (Real.rpow_lt_rpow_left_iff_of_base_lt_one
        ha.left ha.right).mpr yltx
      have hh2: b^x < b^y := (Real.rpow_lt_rpow_left_iff_of_base_lt_one
        hb.left hb.right).mpr yltx
      have hh3: (1:ℝ) < 1 := by
        nth_rw 1 [← hx, ← hy]
        linarith [hh1, hh2]
      norm_num at hh3
  -- almost done.
  have h4: 0 < (2003:ℝ)/2005 ∧ (2003:ℝ)/2005 < 1 := by norm_num
  have h5: 0 < (2004:ℝ)/2005 ∧ (2004:ℝ)/2005 < 1 := by norm_num
  rcases (h2 h4 h5) with ⟨x, hx⟩
  use x
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor <;> intro h
  · apply h3 h4 h5 ?_ hx
    apply h1' y h
  · rw [h]
    apply h1 x hx