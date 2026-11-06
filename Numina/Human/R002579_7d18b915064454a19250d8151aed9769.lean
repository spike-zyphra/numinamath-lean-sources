import Mathlib
namespace algebra_95687
lemma pow_left_injective (hn : n ≠ 0) : Function.Injective (fun a : ℕ => a ^ n) := by
  simp [Function.Injective, le_antisymm_iff, Nat.pow_le_pow_iff_left hn]

lemma pow_left_inj {a b : ℕ} (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (pow_left_injective hn).eq_iff

lemma pow_eq_one : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · simpa [hn] using pow_left_inj hn (b := 1)

theorem log2_two_pow : (2 ^ n).log2 = n := by
  apply Nat.eq_of_le_of_lt_succ <;> simp [Nat.le_log2, Nat.log2_lt, NeZero.ne, Nat.pow_lt_pow_iff_right]
end algebra_95687
/-- Positive integers $a$ and $b$ satisfy the condition\[\log_2(\log_{2^a}(\log_{2^b}(2^{1000}))) = 0.\]Find the sum of all possible values of $a+b$. -/
theorem algebra_95687 (s : Finset (ℕ × ℕ)) (hs : s = {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ Real.logb (2^b) (2^1000) > 0 ∧ Real.logb (2^a) (Real.logb (2^b) (2^1000)) > 0 ∧ Real.logb 2 (Real.logb (2^a) (Real.logb (2^b) (2^1000))) = 0}) : (s.toList.map (fun ⟨a, b⟩ => a + b)).sum = 881 := by
  have em : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ Real.logb (2^b) (2^1000) > 0 ∧ Real.logb (2^a) (Real.logb (2^b) (2^1000)) > 0 ∧ Real.logb 2 (Real.logb (2^a) (Real.logb (2^b) (2^1000))) = 0} = {(1, 500), (2, 250), (3, 125)} := by
    ext x
    obtain ⟨a, b⟩ := x
    simp only [gt_iff_lt, Real.logb_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      false_and, not_false_eq_true, pow_eq_zero_iff, false_or, Set.mem_setOf_eq, Set.mem_insert_iff,
      Prod.mk.injEq, Set.mem_singleton_iff]
    -- clear off false assumptions
    have aw : 0 ≤ (2 : ℝ)^a := by aesop
    have ad : 0 ≤ (2 : ℝ)^b := by aesop
    have s1 : (2 : ℝ)^a ≠ -1 := by linarith
    have s2 : (2 : ℝ)^b ≠ -1 := by linarith
    simp only [OfNat.ofNat_ne_one, s1, s2, (by norm_num : (2 : ℝ) ^ 1000 ≠ 1),
      (by norm_num : (2 : ℝ) ^ 1000 ≠ -1), or_self, or_false, false_or]
    -- we still have some false assumptions
    -- they will get cleared later
    constructor <;> intro h
    · obtain ⟨ha, hb, he, hd, hc | hc | hc | hc⟩ := h
      · norm_num at hc
      · have tan : (2 : ℝ)^a ≠ 1 := by
          intro hc
          have sa : a = 0 := by
            rw [(by norm_num : (2 : ℝ) = ↑(2 : ℕ))] at hc
            norm_cast at hc
            rw [algebra_95687.pow_eq_one] at hc; norm_num at hc
            tauto
          subst a; norm_num at ha
        have tbn : (2 : ℝ)^b ≠ 1 := by
          intro hc
          have sa : b = 0 := by
            rw [(by norm_num : (2 : ℝ) = ↑(2 : ℕ))] at hc
            norm_cast at hc
            rw [algebra_95687.pow_eq_one] at hc; norm_num at hc
            tauto
          subst b; norm_num at hb
        obtain hc | hc | hc | hc := hc
        -- clear off
        · exact False.elim (tan hc)
        -- clear off
        · exact False.elim (tbn hc)
        -- clear off
        · have als := ne_of_lt hd
          symm at als
          simp only [ne_eq, Real.logb_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
          s1, s2, not_false_eq_true, pow_eq_zero_iff, false_or, not_or] at als
          tauto
        -- clear off
        · have := Real.logb_nonneg (b := 2^b) (x := 2^1000) (by aesop) (by norm_num)
          linarith
      -- clear off
      pick_goal 2
      · linarith
      -- solve
      · -- side conditions
        have wal : 1 < (2 : ℝ)^a := by
          rw [(by norm_num : (2 : ℝ) = ↑(2 : ℕ))]
          norm_cast
          have sub : 1 ≤ 2^a := Nat.one_le_two_pow
          obtain wa | wa := eq_or_lt_of_le sub
          · symm at wa
            rw [algebra_95687.pow_eq_one] at wa; norm_num at wa
            subst a; norm_num at ha
          · exact wa
        have wbl : 1 < (2 : ℝ)^b := by
          rw [(by norm_num : (2 : ℝ) = ↑(2 : ℕ))] at *
          norm_cast at *
          have sub : 1 ≤ 2^b := Nat.one_le_two_pow
          obtain wa | wa := eq_or_lt_of_le sub
          · symm at wa
            rw [algebra_95687.pow_eq_one] at wa; norm_num at wa
            subst b; norm_num at hb
          · exact wa
        -- b/1000 = 1/(2^a)
        have sub : Real.logb (2 ^ b) (2 ^ 1000) = 1000 / b := by
          rw [←Real.log_div_log, Real.log_pow, Real.log_pow]
          ring_nf
          simp only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false]
          rw [mul_inv_cancel₀]; norm_num
          -- side condition
          apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num
        rw [sub] at hc
        apply_fun (fun x => ((2 : ℝ)^a)^x) at hc
        rw [Real.rpow_logb (by linarith) (by linarith) (div_pos (by norm_num) (by assumption_mod_cast))] at hc
        norm_num at hc
        have hd : 2^a * b = 1000 := by
          rify; rw [←hc]; ring_nf
          rw [mul_inv_cancel₀ (by norm_cast; linarith)]; norm_num
        have as : b ∈ Nat.divisors 1000 := by simp only [Nat.mem_divisors, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, and_true]; exact Dvd.intro_left _ hd
        rw [(by native_decide : Nat.divisors 1000 = {1, 2, 4, 5, 8, 10, 20, 25, 40, 50, 100, 125, 200, 250, 500, 1000})] at as
        simp only [Finset.mem_insert, Finset.mem_singleton] at as
        obtain xa | xa | xa | xa | xa | xa | xa | xa | xa | xa | xa | xa | xa | xa | xa | xa := as
        all_goals subst b; norm_num at *
        -- clear impossible goals
        all_goals have cl := hc; norm_cast at hc; apply_fun Nat.log2 at hc; simp only [algebra_95687.log2_two_pow] at hc; subst a; norm_num at cl; simp only [Nat.log2, ge_iff_le, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceDiv, Nat.not_ofNat_le_one, zero_add, Nat.reduceAdd] at cl; norm_num at cl
        -- clear feasible goals
        all_goals simp only [Nat.log2, ge_iff_le, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceDiv, Nat.not_ofNat_le_one, zero_add, Nat.reduceAdd]
    -- witnesses
    · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
      -- (1, 500)
      · constructor; norm_num
        constructor; norm_num
        constructor; apply Real.logb_pos; norm_num; norm_num
        constructor
        · apply Real.logb_pos; norm_num
          rw [(by rw [Real.logb_self_eq_one]; norm_num : 1 = Real.logb (2 ^ 500) (2 ^ 500))]
          apply Real.logb_lt_logb <;> norm_num
        right; right; left
        simp only [pow_one]
        rw [(by norm_num : (2 : ℝ) ^ 1000 = (2 : ℝ)^500 * (2 : ℝ)^500)]
        rw [Real.logb_mul, Real.logb_self_eq_one] <;> norm_num
      -- (2, 250)
      · constructor; norm_num
        constructor; norm_num
        constructor; apply Real.logb_pos; norm_num; norm_num
        constructor
        · apply Real.logb_pos; norm_num
          rw [(by norm_num : (2 : ℝ) ^ 1000 = (2 : ℝ)^250 * (2 : ℝ)^250 * (2 : ℝ)^250 * (2 : ℝ)^250)]
          rw [Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_self_eq_one] <;> norm_num
        right; right; left
        rw [(by norm_num : (2 : ℝ) ^ 1000 = (2 : ℝ)^250 * (2 : ℝ)^250 * (2 : ℝ)^250 * (2 : ℝ)^250), (by norm_num : (2 : ℝ)^2 = 4)]
        rw [Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_self_eq_one] <;> norm_num
      -- (3, 125)
      · constructor; norm_num
        constructor; norm_num
        constructor; apply Real.logb_pos; norm_num; norm_num
        constructor
        · apply Real.logb_pos; norm_num
          rw [(by norm_num : (2 : ℝ) ^ 1000 = (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125)]
          rw [Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_self_eq_one] <;> norm_num
        right; right; left
        rw [(by norm_num : (2 : ℝ) ^ 1000 = (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125 * (2 : ℝ)^125), (by norm_num : (2 : ℝ)^3 = 8)]
        rw [Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_mul, Real.logb_self_eq_one] <;> norm_num
  rw [em] at hs
  have aw : s = ({(1, 500), (2, 250), (3, 125)} : Finset (ℕ × ℕ)) := by
    ext x
    rw [←Finset.mem_coe, hs]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  rw [aw]
  -- conclude
  simp only [Finset.sum_to_list, Finset.mem_insert, Prod.mk.injEq, OfNat.one_ne_ofNat,
    Nat.reduceEqDiff, and_self, Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    Nat.reduceAdd, Finset.sum_singleton]