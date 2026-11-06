import Mathlib
/-- The sequence $a_1, a_2, \ldots$ is geometric with $a_1=a$ and common ratio $r,$ where $a$ and $r$ are positive integers. Given that $\log_8 a_1+\log_8 a_2+\cdots+\log_8 a_{12} = 2006,$ find the number of possible ordered pairs $(a,r).$ -/
theorem algebra_93152 :
{(a, r) : ℕ × ℕ | a > 0 ∧ r > 0 ∧ ∑ i ∈ Finset.range 12, Real.logb 8 (a * r ^ i) = 2006}.ncard = 46 := by
  have log2_two_pow n : (2 ^ n).log2 = n := by
    apply Nat.eq_of_le_of_lt_succ <;> simp [Nat.le_log2, Nat.log2_lt, NeZero.ne, Nat.pow_lt_pow_iff_right]
  -- break up algebraic manipulations in stages
  have stg0_pre (a r : ℕ) (ha : 0 < a) (hb : 0 < r) : (∑ i ∈ Finset.range 12, Real.logb 8 (↑a * ↑r ^ i) = 2006) ↔ a ^ 2 * r ^ 11 = 2 ^ 1003 := by
    -- simplify to get $\log_8 (a^{12}r^{66})=2006$
    -- protect 1003 from expansion
    obtain ⟨obs, fos⟩ : ∃ n, n = (1003 : ℕ) := ⟨1003, rfl⟩
    rw [←fos]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    rw [Finset.range_succ]; simp only [Finset.mem_range, lt_self_iff_false, not_false_eq_true, Finset.sum_insert]
    simp only [pow_one, pow_zero, mul_one, Finset.range_zero, Finset.sum_empty, add_zero]
    simp only [←add_assoc]
    repeat rw [←Real.logb_mul]
    · ring_nf
      rw [Real.logb_mul]
      have sw g : Real.logb 8 g = Real.logb 2 g / Real.logb 2 8 := by
        simp only [←Real.log_div_log]
        norm_num
        ring_nf
        simp only [inv_inv, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false]
        simp only [mul_assoc]
        have wle : (Real.log 2)⁻¹ * Real.log 2 = 1 := by
          rw [mul_comm, mul_inv_cancel₀]
          apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num
        rw [wle]; ring
      have wle : Real.logb 2 8 = 3 := by
        rw [(by norm_num : (8 : ℝ) = (2 : ℝ)^(3 : ℝ)), Real.logb_rpow] <;> norm_num
      rw [wle] at sw
      simp only [sw]
      rw [Real.logb_pow, Real.logb_pow]
      ring_nf
      have yew : Real.logb 2 ↑a * 4 + Real.logb 2 ↑r * 22 = 2006 ↔ Real.logb 2 ↑a * 2 + Real.logb 2 ↑r * 11 = 1003 := by
        clear * -; constructor <;> intro wue <;> linarith
      rw [yew]
      -- side condition
      have wlt : 0 < (↑a ^ 2 * ↑r ^ 11 : ℝ) := by
        norm_cast
        apply Nat.zero_lt_of_ne_zero
        intro df
        rw [mul_eq_zero] at df
        obtain df | df := df
        all_goals apply pow_eq_zero at df
        · subst a; norm_num at ha
        · subst r; norm_num at hb
      constructor
      -- forward direction
      · intro hc
        have tmr : a^2 * r^11 = 2^1003 := by
          rw [mul_comm _ (2 : ℝ), mul_comm _ (11 : ℝ), (by norm_num : 2 * Real.logb 2 ↑a = (↑(2 : ℕ) : ℝ) * Real.logb 2 ↑a), (by norm_num : 11 * Real.logb 2 ↑r = (↑(11 : ℕ) : ℝ) * Real.logb 2 ↑r), ←Real.logb_pow, ←Real.logb_pow, ←Real.logb_mul] at hc
          apply_fun (fun x => (2 : ℝ)^x) at hc
          conv at hc =>
            left
            rw [Real.rpow_logb (by norm_num) (by norm_num) wlt]
          exact_mod_cast hc
          -- side conditions:
          all_goals try (norm_num; assumption)
          all_goals intro yy; apply pow_eq_zero at yy; norm_num at yy
          · subst a; norm_num at ha
          · subst r; norm_num at hb
        rw [←fos] at tmr
        exact tmr
      -- reverse direction
      · rw [mul_comm _ (2 : ℝ), mul_comm _ (11 : ℝ), (by norm_num : 2 * Real.logb 2 ↑a = (↑(2 : ℕ) : ℝ) * Real.logb 2 ↑a), (by norm_num : 11 * Real.logb 2 ↑r = (↑(11 : ℕ) : ℝ) * Real.logb 2 ↑r), ←Real.logb_pow, ←Real.logb_pow, ←Real.logb_mul]
        intro sl
        rify at sl; rw [sl]
        rw [(by norm_num : (2 : ℝ)^obs = (2 : ℝ)^(↑obs : ℝ)), Real.logb_rpow (by norm_num) (by norm_num)]
        subst obs
        rfl
        -- side conditions:
        all_goals try (norm_num; assumption)
        all_goals intro yy; apply pow_eq_zero at yy; norm_num at yy
        · subst a; norm_num at ha
        · subst r; norm_num at hb
      all_goals try assumption_mod_cast
      all_goals (intro wt; apply pow_eq_zero at wt; norm_num at wt; omega)
    -- mass solve side conditions
    all_goals norm_cast
    all_goals ring_nf
    all_goals intro wt
    all_goals try (rw [mul_eq_zero] at wt; obtain wt | wt := wt)
    all_goals ((try apply pow_eq_zero at wt); omega)
  have stg0 (a r : ℕ) (ha : 0 < a) (hb : 0 < r) := (stg0_pre a r ha hb).mp
  -- stage 1: prime factorization of a
  have stg1 (a r : ℕ) (ha : 0 < a) (hb : 0 < r) (gt : a ^ 2 * r ^ 11 = 2 ^ 1003) : ∃ v, a = 2^v := by
    rw [(by ring : a ^ 2 * r ^ 11 = a * (a * r^11))] at gt
    have slw : a ∣ 2^1003 := Dvd.intro _ gt
    have sl := Nat.primeFactorsList_sublist_of_dvd slw (by norm_num)
    exists a.primeFactorsList.length
    rw [(by native_decide : Nat.primeFactorsList (2 ^ 1003) = List.replicate 1003 2), List.sublist_replicate_iff] at sl
    obtain ⟨n, hn, he⟩ := sl
    rw [he]; simp only [List.length_replicate]
    apply_fun (fun x => x.prod) at he
    rw [List.prod_replicate, Nat.prod_primeFactorsList (by exact Nat.not_eq_zero_of_lt ha)] at he
    exact he
  -- stage 2: prime factorization of r
  have stg2 (a r : ℕ) (ha : 0 < a) (hb : 0 < r) (gt : a ^ 2 * r ^ 11 = 2 ^ 1003) : ∃ v, r = 2^v := by
    rw [(by ring : a ^ 2 * r ^ 11 = r * (a^2 * r^10))] at gt
    have slw : r ∣ 2^1003 := Dvd.intro _ gt
    have sl := Nat.primeFactorsList_sublist_of_dvd slw (by norm_num)
    exists r.primeFactorsList.length
    rw [(by native_decide : Nat.primeFactorsList (2 ^ 1003) = List.replicate 1003 2), List.sublist_replicate_iff] at sl
    obtain ⟨n, hn, he⟩ := sl
    rw [he]; simp only [List.length_replicate]
    apply_fun (fun x => x.prod) at he
    rw [List.prod_replicate, Nat.prod_primeFactorsList (by exact Nat.not_eq_zero_of_lt hb)] at he
    exact he
  have st : {(a, r) : ℕ × ℕ | a > 0 ∧ r > 0 ∧ ∑ i ∈ Finset.range 12, Real.logb 8 (a * r ^ i) = 2006}.ncard = (Set.Icc 0 45).ncard := by
    apply Set.ncard_congr (fun ⟨_, x⟩ y => (Nat.log2 x - 1) / 2)
    -- (prove a.log2 - 1) / 2 ≤ 45
    · intros a ha
      obtain ⟨a, r⟩ := a
      rw [Set.mem_setOf] at ha
      simp only [gt_iff_lt] at ha
      obtain ⟨ha, hb, hc⟩ := ha
      simp only [Set.mem_Icc, zero_le, true_and]
      have d0 := stg0 a r ha hb hc
      obtain ⟨d1, e1⟩ := stg1 a r ha hb d0
      obtain ⟨d2, e2⟩ := stg2 a r ha hb d0
      rw [e1, e2] at d0

      simp only [log2_two_pow, ge_iff_le]
      conv at d0 =>
        left
        rw [←Nat.pow_mul, ←Nat.pow_mul, ←Nat.pow_add]
      apply congrArg (fun x => x.log2) at d0
      rw [log2_two_pow, log2_two_pow] at d0
      -- prove upper bound
      have wlt : d2 ≤ 91 := by omega
      rw [e2, log2_two_pow]
      -- solve
      clear * - wlt; omega
    · intros a b ha hb hr
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only at hr
      rw [Set.mem_setOf] at ha
      simp only [gt_iff_lt] at ha
      obtain ⟨aa, bb, cc⟩ := ha
      rw [Set.mem_setOf] at hb
      simp only [gt_iff_lt] at hb
      obtain ⟨ff, gg, hh⟩ := hb
      have d0 := stg0 a1 a2 aa bb cc
      obtain ⟨d1, e1⟩ := stg1 a1 a2 aa bb d0
      obtain ⟨d2, e2⟩ := stg2 a1 a2 aa bb d0
      have t0 := stg0 b1 b2 ff gg hh
      obtain ⟨t1, y1⟩ := stg1 b1 b2 ff gg t0
      obtain ⟨t2, y2⟩ := stg2 b1 b2 ff gg t0
      -- now it's time to substitute everything
      subst a1 a2 b1 b2
      conv at d0 =>
        left
        rw [←Nat.pow_mul, ←Nat.pow_mul, ←Nat.pow_add]
      apply congrArg (fun x => x.log2) at d0
      rw [log2_two_pow, log2_two_pow] at d0
      conv at t0 =>
        left
        rw [←Nat.pow_mul, ←Nat.pow_mul, ←Nat.pow_add]
      apply congrArg (fun x => x.log2) at t0
      rw [log2_two_pow, log2_two_pow] at t0
      simp only [log2_two_pow] at *
      -- function is indeed injective
      have lwe : d1 = t1 := by omega
      have lwf : d2 = t2 := by omega
      subst d1 d2
      rfl
    -- function is bijective
    · intros k hk
      simp only [Set.mem_Icc, zero_le, true_and] at hk
      exists (2^(496 - 11 * k), 2^(2 * k + 1))
      constructor
      · simp only [log2_two_pow, add_tsub_cancel_right, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀]
      · rw [Set.mem_setOf]
        constructor
        · apply Nat.two_pow_pos
        · constructor
          · apply Nat.two_pow_pos
          · apply (stg0_pre (2 ^ (496 - 11 * k)) (2 ^ (2 * k + 1)) (by apply Nat.two_pow_pos) (by apply Nat.two_pow_pos)).mpr
            rw [←Nat.pow_mul, ←Nat.pow_mul, ←Nat.pow_add]
            have uew : (496 - 11 * k) * 2 + (2 * k + 1) * 11 = 1003 := by omega
            rw [←uew]
  rw [st]
  -- conclude
  rw [← Set.Nat.card_coe_set_eq]
  simp