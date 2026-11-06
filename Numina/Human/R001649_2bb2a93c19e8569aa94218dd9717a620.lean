import Mathlib

open Real Complex Polynomial Finset

/- We show that |a|*exp (I(θ+2kπ) / m )  is a root of X ^ m - C (|a| ^ m * cexp (I * θ)) -/
lemma isRoot_pos {k : ℕ} {a : ℝ} {θ : ℝ} {m : ℕ} (hm : m > 0) : (X ^ m - C (|a| ^ m * cexp (I * θ))).eval (|a| * cexp (I * (θ + 2 * k * π) / m)) = 0 := by
  simp
  apply sub_eq_zero.mpr
  rw [mul_pow]
  congr
  rw [←zpow_natCast, ←exp_int_mul]
  have hm : (m : ℂ) ≠ 0 := by
    simp
    exact Nat.not_eq_zero_of_lt hm
  field_simp
  rw [mul_add, Complex.exp_add]
  simp
  rw [←exp_nat_mul_two_pi_mul_I k]
  congr 1
  ring

/- We show that |a| * exp (-I (θ + 2kπ) / m) is a root of X ^ m - C (|a| ^ m * cexp (-I * θ)) -/
lemma isRoot_neg {k : ℕ} {a : ℝ} {θ : ℝ} {m : ℕ} (hm : m > 0) : (X ^ m - C (|a| ^ m * cexp (-I * θ))).eval (|a| * cexp (-I * (θ + 2 * k * π) / m)) = 0 := by
  simp
  apply sub_eq_zero.mpr
  rw [mul_pow]
  congr
  rw [←zpow_natCast, ←exp_int_mul]
  have hm : (m : ℂ) ≠ 0 := by
    simp
    exact Nat.not_eq_zero_of_lt hm
  simp
  rw [mul_div_cancel₀ _ hm]
  rw [Complex.exp_neg, Complex.exp_neg]
  congr 1
  rw [mul_add, Complex.exp_add]
  simp
  rw [←exp_nat_mul_two_pi_mul_I k]
  congr 1
  ring

/- Then we show that the roots of X ^ m - C (|a| ^ m * cexp (I * θ)) are exactly |a|*exp (I(θ+2kπ) / m ) for k = 0...m-1. -/
lemma root_pos {a : ℝ} {θ : ℝ} {m : ℕ} (hm : m > 0) :
    (X ^ m - C (|a| ^ m * cexp (I * θ))).roots = (range m).val.map (fun k => |a| * cexp (I * (θ + 2 * k * π) / m)) := by
  by_cases ha : a = 0
  · -- If a = 0, then the polynomial is X^m - C(0) = X^m
    -- and its roots are just 0.
    simp [ha]
    rw [zero_pow, zero_mul, sub_zero]
    simp
    · exact Multiset.nsmul_singleton 0 m
    · exact Nat.not_eq_zero_of_lt hm
  · symm
    -- Otherwise, we first show that |a|*exp (I(θ+2kπ) / m ) for k = 0...m-1 are roots of the polynomial
    -- which is implied by the lemma isRoot_pos
    apply Multiset.eq_of_le_of_card_le
    · apply Multiset.le_iff_subset ?_ |>.mpr
      · intro r
        simp [-map_mul]
        intro k hk hr
        constructor
        · apply ne_zero_of_natDegree_gt (n := 0)
          rw [natDegree_X_pow_sub_C]
          exact hm
        · rw [←hr]
          obtain h := isRoot_pos hm
          simp at h
          rw [h]
      · -- Then we show that the roots are distinct
        refine (Multiset.nodup_map_iff_inj_on ?_).mpr ?_
        · simp
          refine Multiset.Nodup.map_on ?_ ?_
          · simp
          · exact Multiset.nodup_range m
        · simp [ha]
          intro k₁ hk₁ k₂ hk₂ h
          -- We need to show that exp (I(θ+2kπ) / m )  is injective when 0 ≤ k < m.
          -- Assume that exp (I(θ+2k₁π) / m ) = exp (I(θ+2k₂π) / m )
          apply Complex.exp_eq_exp_iff_exists_int.mp at h
          obtain ⟨n, hn⟩ := h
          apply sub_eq_zero.mpr at hn
          -- There exists n such that I(θ + 2k₁π) / m - I(θ + 2k₂π) / m = n * 2 * π * I
          have : I * π * ((k₁ - k₂) / m - n) * 2 = 0 := by
            rw [←hn]
            ring_nf
          simp [pi_ne_zero] at this
          apply sub_eq_zero.mp at this
          -- However, since k₁ k₂ < m, n must be in the range -1 < n < 1
          -- and we can conclude that n = 0
          have hn : |n| < (1 : ℝ) := by
            apply congrArg norm at this
            nth_rw 2 [Complex.norm_eq_abs] at this
            rw [abs_intCast] at this
            simp
            rw [←this, norm_div]
            apply div_lt_iff₀ ?_ |>.mpr
            · norm_cast
              simp
              apply abs_lt.mpr
              constructor
              · rw [Int.subNatNat_eq_coe]
                simp
                norm_cast
                exact Nat.lt_add_right k₁ hk₂
              · rw [Int.subNatNat_eq_coe]
                apply sub_left_lt_of_lt_add
                norm_cast
                exact Nat.lt_add_left k₂ hk₁
            · simp [hm]
          -- So k₁ = k₂.
          norm_cast at hn
          simp at hn
          simp [hn] at this
          rcases this with h | h
          . apply sub_eq_zero.mp at h
            simp at h
            exact h
          · simp [h] at hm
    · -- Finally, we have obtained m distinct roots, but all the roots of the polynomial
      -- are exactly the degree of the polynomial, which is m.
      -- So we can conclude that the roots are exactly the ones we have found.
      apply le_trans (card_roots' _)
      apply le_of_eq
      rw [natDegree_X_pow_sub_C]
      simp

/- We show that the roots of X ^ m - C (|a| ^ m * cexp (-I * θ)) are exactly |a|*exp (-I(θ+2kπ) / m ) for k = 0...m-1. -/
lemma root_neg {a : ℝ} {θ : ℝ} {m : ℕ} (hm : m > 0) :
    (X ^ m - C (|a| ^ m * cexp (-I * θ))).roots = (range m).val.map (fun k => |a| * cexp (-I * (θ + 2 * k * π) / m)) := by
  by_cases ha : a = 0
  · -- If a = 0, then the polynomial is X^m - C(0) = X^m
    -- and its roots are just 0.
    simp [ha]
    rw [zero_pow, zero_mul, sub_zero]
    simp
    · exact Multiset.nsmul_singleton 0 m
    · exact Nat.not_eq_zero_of_lt hm
  · -- Otherwise, we first show that |a|*exp (-I(θ+2kπ) / m ) for k = 0...m-1 are roots of the polynomial
    -- which is implied by the lemma isRoot_neg
    symm
    apply Multiset.eq_of_le_of_card_le
    · apply Multiset.le_iff_subset ?_ |>.mpr
      · intro r
        simp [-map_mul]
        intro k hk hr
        constructor
        · apply ne_zero_of_natDegree_gt (n := 0)
          rw [natDegree_X_pow_sub_C]
          exact hm
        · rw [←hr]
          obtain h := isRoot_neg hm
          simp at h
          rw [h]
      · -- Then we show that the roots are distinct
        refine (Multiset.nodup_map_iff_inj_on ?_).mpr ?_
        · simp
          refine Multiset.Nodup.map_on ?_ ?_
          · simp
          · exact Multiset.nodup_range m
        · simp [ha]
          intro k₁ hk₁ k₂ hk₂ h
          apply Complex.exp_eq_exp_iff_exists_int.mp at h
          obtain ⟨n, hn⟩ := h
          apply sub_eq_zero.mpr at hn
          have : I * π * ((k₂ - k₁) / m - n) * 2 = 0 := by
            rw [←hn]
            ring_nf
          simp [pi_ne_zero] at this
          apply sub_eq_zero.mp at this
          have hn : |n| < (1 : ℝ) := by
            apply congrArg norm at this
            nth_rw 2 [Complex.norm_eq_abs] at this
            rw [abs_intCast] at this
            simp
            rw [←this, norm_div]
            apply div_lt_iff₀ ?_ |>.mpr
            · norm_cast
              simp
              apply abs_lt.mpr
              constructor
              · rw [Int.subNatNat_eq_coe]
                simp
                norm_cast
                exact Nat.lt_add_right k₂ hk₁
              · rw [Int.subNatNat_eq_coe]
                apply sub_left_lt_of_lt_add
                norm_cast
                exact Nat.lt_add_left k₁ hk₂
            · simp [hm]
          norm_cast at hn
          simp at hn
          simp [hn] at this
          rcases this with h | h
          . apply sub_eq_zero.mp at h
            simp at h
            rw [h]
          · simp [h] at hm
    · -- Finally, we have obtained m distinct roots, but all the roots of the polynomial
      -- are exactly the degree of the polynomial, which is m.
      -- So we can conclude that the roots are exactly the ones we have found.
      apply le_trans (card_roots' _)
      apply le_of_eq
      rw [natDegree_X_pow_sub_C]
      simp

/- We show that X ^ m - |a| ^ m exp (Iθ) = ∏ k ∈[0, m-1], (X - |a|exp (I * (θ + 2 * k * π) / m)). -/
lemma pos_eq_prod {a : ℝ} {θ : ℝ} {m : ℕ} (hm : m > 0) :
    X ^ m - C (|a| ^ m * cexp (I * θ)) = ∏ k in range m, (X - C (|a| * cexp (I * (θ + 2 * k * π) / m))) := by
  apply Eq.trans (eq_prod_roots_of_splits_id ?_) ?_
  · exact IsAlgClosed.splits (X ^ m - C (↑|a| ^ m * cexp (I * ↑θ)))
  · -- Since the polynomial splits, we can use lemma root_pos to express it as a product of X - |a| * exp (I(θ + 2kπ) / m)
    rw [root_pos hm]
    have : C (X ^ m - C (|a| ^ m * cexp (I * θ))).leadingCoeff = 1 := by
      rw [leadingCoeff_X_pow_sub_C]
      · simp
      · exact hm
    rw [this]
    simp
    exact rfl

/- We show that X ^ m - |a| ^ m exp (-Iθ) = ∏ k ∈[0, m-1], (X - |a|exp (-I * (θ + 2 * k * π) / m)). -/
lemma neg_eq_prod {a : ℝ} {θ : ℝ} {m : ℕ} (hm : m > 0) :
    X ^ m - C (|a| ^ m * cexp (-I * θ)) = ∏ k in range m, (X - C (|a| * cexp (-I * (θ + 2 * k * π) / m))) := by
  apply Eq.trans (eq_prod_roots_of_splits_id ?_) ?_
  · exact IsAlgClosed.splits (X ^ m - C (↑|a| ^ m * cexp (-I * ↑θ)))
  · -- Since the polynomial splits, we can use lemma root_neg to express it as a product of X - |a| * exp (-I(θ + 2kπ) / m)
    rw [root_neg hm]
    have : C (X ^ m - C (|a| ^ m * cexp (-I * θ))).leadingCoeff = 1 := by
      rw [leadingCoeff_X_pow_sub_C]
      · simp
      · exact hm
    rw [this]
    simp
    exact rfl

/-16. (CUB 2) Given $a, \theta \in \mathbb{R}, m \in \mathbb{N}$, and $P(x)=x^{2 m}-2|a|^{m} x^{m} \cos m\theta+a^{2 m}$, factorize $P(x)$ as a product of $m$ real quadratic polynomials.-/
theorem algebra_24978 (a : ℝ) (θ : ℝ) (m : ℕ) (hm : m > 0) (P : ℝ[X])
    (hP : P = X ^ (2 * m) - C (2 * |a| ^ m * Real.cos θ) * X ^ m + C a ^ (2 * m)) :
    (∀ k ∈ range m, (X ^ 2 - C (2 * |a| * Real.cos ((θ + 2 * k * π) / m)) * X + C a ^ 2).natDegree = 2) ∧
    P = ∏ k ∈ range m, (X ^ 2 - C (2 * |a| * Real.cos ((θ + 2 * k * π) / m)) * X + C a ^ 2) := by

  constructor
  · -- We prove that each factor has degree 2
    intro k hk
    rw [←C_pow, natDegree_add_C]
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · by_cases h : 2 * |a| * Real.cos ((θ + 2 * ↑k * π) / ↑m) ≠ 0
      · rw [natDegree_C_mul h]
        simp
      · push_neg at h
        simp [h]
  · -- We show that P can be expressed as a product of the quadratic factors
    -- First, we cast the polynomial into ℂ[X]
    apply Polynomial.map_injective (Complex.ofRealHom)
    · exact RingHom.injective ofRealHom
    · simp [hP]
      -- Then, note that P = (X ^ m - |a| ^ m * cexp (I * θ)) * (X ^ m - |a| ^ m * cexp (-I * θ))
      trans (X ^ m - C (|a| ^ m * cexp (I * θ))) * (X ^ m - C (|a| ^ m * cexp (-I * θ)))
      · rw [mul_comm I, exp_mul_I]
        have : - I * θ = (-θ) * I := by
          ring
        rw [this, exp_mul_I]
        apply Polynomial.funext
        simp
        ring_nf
        rw [Complex.sin_sq]
        simp
        ring_nf
        rw [mul_comm, pow_mul, pow_mul]
        congr 1
        norm_cast
        simp
      · -- By our lemmas,
        -- X^m - |a|^m * cexp (I * θ) = ∏ k in range m, (X - |a| * cexp (I * (θ + 2 * k * π) / m))
        -- and X^m - |a|^m * cexp (-I * θ) = ∏ k in range m, (X - |a| * cexp (-I * (θ + 2 * k * π) / m))
        rw [pos_eq_prod hm, neg_eq_prod hm]
        rw [←prod_mul_distrib]
        -- Therefore, P = ∏ k in range m, (X - |a| * cexp (I * (θ + 2 * k * π) / m)) * (X - |a| * cexp (-I * (θ + 2 * k * π) / m))
        rw [Polynomial.map_prod]
        simp
        apply prod_congr rfl
        -- The result follows from the fact that
        -- (X - |a| * cexp (I * (θ + 2 * k * π) / m)) * (X - |a| * cexp (-I * (θ + 2 * k * π) / m)) = X ^ 2 - 2 * |a| * Real.cos ((θ + 2 * k * π) / m) * X + a ^ 2
        intro k hk
        apply Polynomial.funext
        intro z
        apply sub_eq_zero.mp
        simp [Complex.cos]
        ring_nf
        simp [mul_assoc, ←Complex.exp_add]
        norm_cast
        simp
