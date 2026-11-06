import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Set.Card

/- Determine the number of ordered pairs (a,b) of integers such that log⁡ab+6log⁡ba=5, 2≤a≤2005, 2≤b≤2005. -/

theorem AIME_Algebra_729 : Set.encard {⟨a,b⟩ : ℕ × ℕ | 2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ ((Real.logb a b) + 6*(Real.logb b a) = 5)} = 54 := by

  -- Auxiliary lemmas to deduce invertibility of log
  have apos {a : ℕ} (ha : a ≥ 2) : (a : ℝ) > 0 := by simp only [gt_iff_lt, Nat.cast_pos]; linarith
  have ainv {a : ℕ} (ha : a ≥ 2) : Real.log a ≠ 0 := by
    rw [Real.log_ne_zero]
    exact ⟨by simp only [ne_eq, Nat.cast_eq_zero]; linarith,
            by simp only [ne_eq, Nat.cast_eq_one]; linarith,
            by simp only [ne_eq]; linarith⟩

  -- We rewrite the equation
  have (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (h : (Real.logb a b) + (6:ℕ)*(Real.logb b a) = 5) :
      (Real.log b - (3 : ℕ)*Real.log a) * (Real.log b - (2 : ℕ)*Real.log a) = 0 := by
    repeat rw [← Real.log_div_log] at h
    apply congrArg (HMul.hMul ((Real.log a)*(Real.log b))) at h
    ring_nf at h
    rw [mul_comm] at h
    simp only [isUnit_iff_ne_zero, ne_eq, ainv ha, not_false_eq_true, IsUnit.inv_mul_cancel_left,
      ainv hb, mul_inv_cancel_right₀] at h
    rw [← sub_eq_zero] at h
    rw [← h]
    ring_nf

  -- We deduce the possible values of a and b
  have : ∀ (a b : ℕ), (2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ ((Real.logb a b) + 6*(Real.logb b a)
       = 5)) ↔ (2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ (b = a^2 ∨ b = a^3)) := by
    intro a b
    constructor
    · intro ⟨ha1, ha2, hb1, hb2, h⟩
      simp only [ha1, ha2, hb1, hb2, true_and]
      apply this a b ha1 hb1 at h
      rw [mul_eq_zero, ← Real.log_rpow (apos ha1), ← Real.log_rpow (apos ha1)] at h
      rcases h with h | h
      · rw [sub_eq_zero] at h
        apply Real.log_injOn_pos at h
        · right
          exact_mod_cast h
        · simp only [Set.mem_Ioi, Nat.cast_pos]
          linarith
        · simp only [Set.mem_Ioi, Nat.cast_pos]
          rw_mod_cast [Odd.pow_pos_iff]
          · linarith
          · exact Nat.odd_iff.mpr rfl
      · rw [sub_eq_zero] at h
        apply Real.log_injOn_pos at h
        · left
          exact_mod_cast h
        · simp only [Set.mem_Ioi, Nat.cast_pos]
          linarith
        · simp only [Set.mem_Ioi, Nat.cast_pos]
          rw [Real.rpow_natCast]
          exact sq_pos_of_pos (apos ha1)
    · intro ⟨ha1, ha2, hb1, hb2, h⟩
      simp only [ha1, ha2, hb1, hb2, true_and]
      rw [← Real.logb_rpow_eq_mul_logb_of_pos (apos ha1)]
      rcases h with h | h
      · rw [h, ← Real.log_div_log, ← Real.log_div_log]
        simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
        rw [Real.log_rpow (apos ha1)]
        ring_nf
        simp [ainv ha1]
      · rw [h, ← Real.log_div_log, ← Real.log_div_log]
        simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
        rw [Real.log_rpow (apos ha1)]
        ring_nf
        simp [ainv ha1]
  simp_rw [this]

  -- We have two families of solutions
  have union : {⟨a,b⟩ : ℕ × ℕ | 2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ (b = a^2 ∨ b = a^3)} = {⟨a,b⟩ : ℕ × ℕ | 2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ b = a^2} ∪ {⟨a,b⟩ : ℕ × ℕ | 2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ b = a^3} := by
    ext ⟨a,b⟩
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro ⟨ha1, ha2, hb1, hb2, hab⟩
      rcases hab with hab | hab
      · left; exact ⟨ha1, ha2, hb1, hb2, hab⟩
      · right; exact ⟨ha1, ha2, hb1, hb2, hab⟩
    · intro h
      rcases h with h | h
      · rcases h with ⟨ha1, ha2, hb1, hb2, hab⟩
        exact ⟨ha1, ha2, hb1, hb2, Or.inl hab⟩
      · rcases h with ⟨ha1, ha2, hb1, hb2, hab⟩
        exact ⟨ha1, ha2, hb1, hb2, Or.inr hab⟩

  -- The two families are disjoint
  have disjoint : Disjoint {⟨a,b⟩ : ℕ × ℕ | 2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ b = a^2}
      {⟨a,b⟩ : ℕ × ℕ | 2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ b = a^3} := by
    intro S h2 h3 ⟨a, b⟩ hs
    exfalso
    simp only [Set.le_eq_subset] at h2 h3
    have h2' : b = a^2 := by
      let h := h2 hs
      simp only [Set.mem_setOf_eq] at h
      exact h.2.2.2.2
    have h3' : b = a^3 := by
      let h := h3 hs
      simp only [Set.mem_setOf_eq] at h
      exact h.2.2.2.2
    have ge2 : a ≥ 2 := by
      let h := h2 hs
      simp only [Set.mem_setOf_eq] at h
      exact h.1
    rw [h2'] at h3'
    nth_rw 2 [pow_succ] at h3'
    nth_rw 1 [← mul_one (a^2)] at h3'
    apply mul_left_cancel₀ at h3'
    linarith
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact Nat.not_eq_zero_of_lt ge2

  -- We compute the cardinality of the first family
  have bij₁ : {⟨a,b⟩ : ℕ × ℕ | 2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ b = a^2}
      ≃ Finset.Icc 2 44 := by
    symm
    apply Equiv.ofBijective ?_ ?_
    · intro ⟨a, ha⟩
      use ⟨a, a^2⟩
      rw [Finset.mem_Icc] at ha
      simp only [Set.mem_setOf_eq, and_true]
      exact ⟨ha.1, le_trans ha.2 (by linarith), le_trans ha.1 (Nat.le_self_pow (by linarith) a), le_trans (Nat.pow_le_pow_left ha.2 2) (by norm_num)⟩
    · constructor
      · intro ⟨x, hx⟩
        simp only [Finset.mem_Icc] at hx
        simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall, Subtype.mk.injEq, Prod.forall]
        intro a _ hab
        have : (x, x^2).1 = (a, a^2).1 := by rw [hab]
        exact this
      · intro ⟨⟨a, b⟩, hab⟩
        simp only [Set.mem_setOf_eq] at hab
        obtain ⟨ha1, ha2, hb1, hb2, hab⟩ := hab
        have : a ≤ 44 := by
          rw [hab] at hb2
          rw [← Nat.le_sqrt'] at hb2
          norm_num at hb2
          exact hb2
        use ⟨a, ?_⟩
        · simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq, Prod.mk.injEq, true_and]
          exact hab.symm
        · rw [Finset.mem_Icc]
          exact ⟨ha1, this⟩

  have card₁ : Set.encard {⟨a,b⟩ : ℕ × ℕ | 2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ b = a^2} = Finset.card (Finset.Icc 2 44) := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    apply Set.encard_congr
    exact bij₁

  -- We compute the cardinality of the second family
  have bij₂ : {⟨a,b⟩ : ℕ × ℕ | 2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ b = a^3}
      ≃ Finset.Icc 2 12 := by
    symm
    apply Equiv.ofBijective ?_ ?_
    · intro ⟨a, ha⟩
      use ⟨a, a^3⟩
      rw [Finset.mem_Icc] at ha
      simp only [Set.mem_setOf_eq, and_true]
      exact ⟨ha.1, le_trans ha.2 (by linarith), le_trans ha.1 (Nat.le_self_pow (by linarith) a), le_trans (Nat.pow_le_pow_left ha.2 3) (by norm_num)⟩
    · constructor
      · intro ⟨x, hx⟩
        simp only [Finset.mem_Icc] at hx
        simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall, Subtype.mk.injEq, Prod.forall]
        intro a _ hab
        have : (x, x^3).1 = (a, a^3).1 := by rw [hab]
        exact this
      · intro ⟨⟨a, b⟩, hab⟩
        simp only [Set.mem_setOf_eq] at hab
        obtain ⟨ha1, ha2, hb1, hb2, hab⟩ := hab
        use ⟨a, ?_⟩
        · simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq, Prod.mk.injEq, true_and]
          exact hab.symm
        · rw [Finset.mem_Icc]
          constructor
          · exact ha1
          · rw [hab] at hb2
            by_contra!
            have : 13 ≤ a := this
            have h : 3 ≠ 0 := by norm_num
            rw [← Nat.pow_le_pow_iff_left h] at this
            simp only [Nat.reducePow] at this
            linarith

  have card₂ : Set.encard {⟨a,b⟩ : ℕ × ℕ | 2 ≤ a ∧ a ≤ 2005 ∧ 2 ≤ b ∧ b ≤ 2005 ∧ b = a^3} = Finset.card (Finset.Icc 2 12) := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    apply Set.encard_congr
    exact bij₂

  -- We substitute the values and complete the computation
  rw [union, Set.encard_union_eq disjoint, card₁, card₂]
  norm_num