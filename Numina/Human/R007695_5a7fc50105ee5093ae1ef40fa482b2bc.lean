import Mathlib
set_option maxHeartbeats 999999999
set_option maxRecDepth 999999999
/-- For positive integer $n$, let $s(n)$ denote the sum of the digits of $n$. Find the smallest positive integer satisfying $s(n) = s(n+864) = 20$. -/
theorem number_theory_96331 :
IsLeast {n | 0 < n ∧ (Nat.digits 10 n).sum = 20 ∧ (Nat.digits 10 (n + 864)).sum = 20} 695 := by
  constructor
  -- witness satisfies conditions
  · native_decide
  -- no smaller witness
  · intros n hn
    obtain ⟨hn, ht, hu⟩ := hn
    by_cases ha : 695 ≤ n
    · exact ha
    have hb : n < 695 := by exact Nat.gt_of_not_le ha
    have als := Nat.le_digits_len_le 10 n 999 (Nat.le_trans (Nat.le_of_lt_succ hb) (by decide))
    rw [(by native_decide : (Nat.digits 10 999).length = 3)] at als
    -- we will prove the number has exactly 3 digits
    obtain al | al | al | al : (Nat.digits 10 n).length = 0 ∨ (Nat.digits 10 n).length = 1 ∨ (Nat.digits 10 n).length = 2 ∨ (Nat.digits 10 n).length = 3 := by clear * - als; omega
    -- zero digits, this means n = 0
    · have lwe : Nat.digits 10 n = [] := by
        simp only [List.length_eq_zero] at al
        exact al
        
      rw [Nat.digits_eq_nil_iff_eq_zero] at lwe
      subst n; norm_num at *
    -- one digit, let's see how this fares
    · have da := Nat.digits_def' (b := 10) (by decide) (n := n) hn
      rw [da] at al
      simp only [Nat.reduceLeDiff, List.length_cons, add_left_eq_self,
        List.length_eq_zero] at al
      rw [al] at da
      rw [da] at ht
      rw [Nat.digits_eq_nil_iff_eq_zero] at al
      norm_num at ht
      omega
      -- contradiction!
    -- now we have two digits
    · have da := Nat.digits_def' (b := 10) (by decide) (n := n) hn
      have wle : n / 10 ≠ 0 := by
        rw [da] at al
        norm_num at al
        rw [←Nat.digits_ne_nil_iff_ne_zero (b := 10)]
        intro ga
        rw [ga] at al
        norm_num at al
      -- we can split further
      have db := Nat.digits_def' (b := 10) (by decide) (n := n / 10) (Nat.pos_of_ne_zero wle)
      rw [db] at da
      rw [da] at al
      simp only [Nat.reduceLeDiff, List.length_cons, Nat.reduceEqDiff,
        List.length_eq_zero] at al
      rw [al] at da
      rw [da] at ht
      -- get sum of digits
      simp only [List.sum_cons, List.sum_nil, add_zero] at ht
      omega
    -- now we have three digits, we can work further
    have da := Nat.digits_def' (b := 10) (by decide) (n := n) hn
    have wle : n / 10 ≠ 0 := by
      rw [da] at al
      norm_num at al
      rw [←Nat.digits_ne_nil_iff_ne_zero (b := 10)]
      intro ga
      rw [ga] at al
      norm_num at al
    -- we can split further
    have db := Nat.digits_def' (b := 10) (by decide) (n := n / 10) (Nat.pos_of_ne_zero wle)
    rw [db] at da
    rw [da] at al
    simp only [Nat.reduceLeDiff, List.length_cons, Nat.reduceEqDiff,
      List.length_eq_zero] at al
    have wle : n / 10 / 10 ≠ 0 := by
      rw [←Nat.digits_ne_nil_iff_ne_zero (b := 10)]
      intro ga
      rw [ga] at al
      norm_num at al
    have dc := Nat.digits_def' (b := 10) (by decide) (n := n / 10 / 10) (Nat.pos_of_ne_zero wle)
    rw [dc] at da al
    simp only [Nat.reduceLeDiff, List.length_cons, add_left_eq_self, List.length_eq_zero] at al
    rw [al] at da
    rw [da] at ht
    norm_num at ht
    -- list every possible option and refute
    rw [Nat.div_div_eq_div_mul] at ht
    norm_num at ht
    have ta := Nat.lt_base_pow_length_digits (b := 10) (m := n)
    rw [da] at ta
    norm_num at ta

    -- enumerate all possible n values
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : n = 299 ∨ n = 389 ∨ n = 398 ∨ n = 479 ∨ n = 488 ∨ n = 497 ∨ n = 569 ∨ n = 578 ∨ n = 587 ∨ n = 596 ∨ n = 659 ∨ n = 668 ∨ n = 677 ∨ n = 686 ∨ n = 695 ∨ n = 749 ∨ n = 758 ∨ n = 767 ∨ n = 776 ∨ n = 785 ∨ n = 794 ∨ n = 839 ∨ n = 848 ∨ n = 857 ∨ n = 866 ∨ n = 875 ∨ n = 884 ∨ n = 893 ∨ n = 929 ∨ n = 938 ∨ n = 947 ∨ n = 956 ∨ n = 965 ∨ n = 974 ∨ n = 983 ∨ n = 992 := by
      obtain ⟨a, ha⟩ : ∃ a, a = n % 10 := ⟨n % 10, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b, b = (n / 10) % 10 := ⟨(n / 10) % 10, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c, c = (n / 100) % 10 := ⟨(n / 100) % 10, rfl⟩
      have ew : n = a + 10 * b + 100 * c := by
        have esw : (n / 100) % 10 = n / 100 := by omega
        rw [esw] at hc; rw [hc, hb, ha]
        omega
      have wa : a < 10 := by rw [ha]; exact Nat.mod_lt _ (by norm_num)
      have wb : b < 10 := by rw [hb]; exact Nat.mod_lt _ (by norm_num)
      have wc : c < 10 := by rw [hc]; exact Nat.mod_lt _ (by norm_num)
      rw [←ha, ←hb, ←hc] at ht
      have ey : 1 ≤ a := by omega
      subst n
      clear * - wa wb wc ht ey
      -- now it is a system of linear equations
      omega
    all_goals norm_num at *