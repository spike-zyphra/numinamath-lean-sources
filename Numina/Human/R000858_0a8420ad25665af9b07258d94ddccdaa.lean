import Mathlib

/- On the graph of $y=(x+2)^4-100$, how many points are there whose coordinates are both negative integers? -/
theorem algebra_18659 (f : ℝ → ℝ) (hf : f = fun x => (x + 2)^4 - 100) :
    Set.ncard {p : ℤ × ℤ | p.1 < 0 ∧ p.2 < 0 ∧ f p.1 = p.2} = 5 := by
  have eq : {p : ℤ × ℤ | p.1 < 0 ∧ p.2 < 0 ∧ f p.1 = p.2} = {(-1, -99), (-2, -100), (-3, -99), (-4, -84), (-5, -19)} := by
    ext p
    constructor
    intro pin
    rcases pin with ⟨p1lt, p2lt, fpeq⟩
    -- $-5 \le p.1 < 0$, so $p.1 = -5, -4, -3, -2, -1$
    have pge : -5 ≤ p.1 := by
      have pge : -5 ≤ (p.1 : ℝ) := by
        have neg : (p.2 : ℝ) < 0 := by
          exact Int.cast_lt_zero.mpr p2lt
        simp only [← fpeq, hf, sub_neg] at neg
        by_contra contra
        rw [not_le] at contra
        have lt : (p.1 : ℝ) < (-5 : ℤ) := by
          simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat]
          exact contra
        have lt2 : p.1 < -5 := by
          by_contra contra1
          rw [not_lt] at contra1
          have : (-5 : ℤ) ≤ (p.1 : ℝ) := by
            exact Int.cast_le.mpr contra1
          linarith
        have le : p.1 ≤ -6 := by
          exact Int.lt_add_one_iff.mp lt2
        have le1 : (p.1 : ℝ) ≤ (-6 : ℤ) := by
          exact Int.cast_le.mpr le
        simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat] at le1
        have le2 : (p.1 : ℝ) + 2 ≤ -4 := by
          linarith
        have le3 : (-4) ^ 2 ≤ ((p.1 : ℝ) + 2) ^ 2 := by
          nlinarith
        have le4 : ((-4) ^ 2) ^ 2 ≤ (((p.1 : ℝ) + 2) ^ 2) ^2 := by
          nlinarith
        nlinarith
      by_contra contra
      simp only [Int.reduceNeg, ge_iff_le, not_le] at contra
      have : (p.1 : ℝ) < (-5 : ℤ) := by
        exact Int.cast_lt.mpr contra
      simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat] at this
      linarith
    let x := p.1
    have xeq : p.1 = x := by
      exact rfl
    rw [xeq] at pge
    rw [xeq] at p1lt
    interval_cases x
    · -- when $p.1 = -5, p = (-5, -19)$
      have peq : p = (-5, -19) := by
        ext
        simp only [xeq, Int.reduceNeg]
        simp only [hf, xeq, Int.reduceNeg, Int.cast_neg, Int.cast_ofNat] at fpeq
        ring_nf at fpeq
        have p2eq : (p.2 : ℝ) = (-19 : ℤ) := by
          rw [← fpeq]
          simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat]
        simp only [Int.reduceNeg]
        exact Int.cast_injective p2eq
      rw [peq]
      exact PEquiv.mem_ofSet_self_iff.mp rfl
    · -- when $p.1 = -4, p = (-4, -84)$
      have peq : p = (-4, -84) := by
        ext
        simp only [xeq, Int.reduceNeg]
        simp only [hf, xeq, Int.reduceNeg, Int.cast_neg, Int.cast_ofNat] at fpeq
        ring_nf at fpeq
        have p2eq : (p.2 : ℝ) = (-84 : ℤ) := by
          rw [← fpeq]
          simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat]
        simp only [Int.reduceNeg]
        exact Int.cast_injective p2eq
      rw [peq]
      exact PEquiv.mem_ofSet_self_iff.mp rfl
    · -- when $p.1 = -3, p = (-3, -99)$
      have peq : p = (-3, -99) := by
        ext
        simp only [xeq, Int.reduceNeg]
        simp only [hf, xeq, Int.reduceNeg, Int.cast_neg, Int.cast_ofNat] at fpeq
        ring_nf at fpeq
        have p2eq : (p.2 : ℝ) = (-99 : ℤ) := by
          rw [← fpeq]
          simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat]
        simp only [Int.reduceNeg]
        exact Int.cast_injective p2eq
      rw [peq]
      exact PEquiv.mem_ofSet_self_iff.mp rfl
    · -- when $p.1 = -2, p = (-2, -100)$
      have peq : p = (-2, -100) := by
        ext
        simp only [xeq, Int.reduceNeg]
        simp only [hf, xeq, Int.reduceNeg, Int.cast_neg, Int.cast_ofNat] at fpeq
        ring_nf at fpeq
        have p2eq : (p.2 : ℝ) = (-100 : ℤ) := by
          rw [← fpeq]
          simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat]
        simp only [Int.reduceNeg]
        exact Int.cast_injective p2eq
      rw [peq]
      exact PEquiv.mem_ofSet_self_iff.mp rfl
    · -- when $p.1 = -1, p = (-1, -99)$
      have peq : p = (-1, -99) := by
        ext
        simp only [xeq, Int.reduceNeg]
        simp only [hf, xeq, Int.reduceNeg, Int.cast_neg, Int.cast_ofNat] at fpeq
        ring_nf at fpeq
        have p2eq : (p.2 : ℝ) = (-99 : ℤ) := by
          rw [← fpeq]
          simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat]
        simp only [Int.reduceNeg]
        exact Int.cast_injective p2eq
      rw [peq]
      exact PEquiv.mem_ofSet_self_iff.mp rfl
    intro pin
    rcases pin with peq | peq | peq | peq | peq
    all_goals
    rw [peq]
    simp only [hf, Int.reduceNeg, Set.mem_setOf_eq, Left.neg_neg_iff, zero_lt_one, Nat.ofNat_pos, Int.cast_neg, Int.cast_one, Int.cast_ofNat, true_and]
    norm_num
  -- so the cardinality is $5$
  rw [eq]
  norm_num