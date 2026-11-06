import Mathlib

/- Find the valuation...

(i) 3-adic of $A=2^{27}+1$.

(ii) 7-adic of $B=161^{14}-112^{14}$.

(iii) 2-adic of $C=7^{20}+1$.

(iv) 2-adic of $D=17^{48}-5^{48}$. -/
theorem number_theory_131848 :
    (Nat.factorization (2^27 + 1) 3) = 4 ∧
    (Nat.factorization (161^14 - 112^14) 7) = 16 ∧
    (Nat.factorization (7^20 + 1) 2) = 1 ∧
    (Nat.factorization (17^48 - 5^48) 2) = 6 := by
  -- native_decide can prove this theorem automatically.
  -- Consider a more detailed proof
  constructorm* _ ∧ _
  · rw [Nat.factorization_def _ Nat.prime_three]
    -- Apply LTE to v_3(2^27 + 1^27) and get v_3(3) + v_3(27) = 1 + 3 = 4
    rw [show 1 = 1 ^ 27 by norm_num, padicValNat.pow_add_pow (by decide) (by norm_num) (by norm_num) (by decide)]
    rw [show 27 = 3 ^ 3 by norm_num, padicValNat.prime_pow]
    norm_num
  · rw [Nat.factorization_def _ (by norm_num)]
    -- We have 161 ^ 14 - 112 ^ 14 = 7 ^ 14 * (23 ^ 14 - 16 ^ 14).
    -- So v_7(161 ^ 14 - 112 ^ 14) = 14 + v_7(23 ^ 14 - 16 ^ 14).
    rw [show 161 ^ 14 - 112 ^ 14 = 7 ^ 14 * (23 ^ 14 - 16 ^ 14) by norm_num]
    have p7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    rw [padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
    -- Apply LTE to v_7(23 ^ 14 - 16 ^ 14) and get v_7(7) + v_7(14) = 1 + 1 = 2
    rw [padicValNat.pow_sub_pow (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    rw [show 14 = 7 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num)]
    rw [padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  · have ⟨k, hk⟩ : ∃ k, 7 ^ 20 + 1 = 2 * (2 * k + 1) := by
      -- Show that 7 ^ 20 + 1 = 2 * (2 * k + 1) for some k.
      -- We have 7 ^ 20 + 1 ≡ 2 [MOD 4]
      have h4 : 7 ^ 20 + 1 ≡ 2 [MOD 4] := by decide
      -- We conclude that 7 ^ 20 + 1 = 4 * k + 2 for some k
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (by norm_num)] at h4
      have ⟨k, hk⟩ := h4
      use k
      rw [show 2 * (2 * k + 1) = 4 * k + 2 by ring, ←hk]
      norm_num
    -- v_2(2 * (2 * k + 1)) = 1 + v_2(2 * k + 1) = 1 + 0 = 1
    rw [hk, Nat.factorization_def _ Nat.prime_two]
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat_self]
    rw [padicValNat.eq_zero_of_not_dvd (by omega)]
  · rw [Nat.factorization_def _ Nat.prime_two]
    apply Nat.add_right_cancel (m := 1)
    -- Apply LTE to v_2(17 ^ 48 - 5 ^ 48) + 1 and get v_2(22) + v_2(12) + v_2(48) = 1 + 2 + 4 = 7
    rw [padicValNat.pow_two_sub_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)]
    rw [show 17 + 5 = 2 * 11 by norm_num, show 17 - 5 = 2 ^ 2 * 3 by norm_num, show 48 = 2 ^ 4 * 3 by norm_num]
    repeat rw [padicValNat.mul (by norm_num) (by norm_num)]
    simp_rw [padicValNat.prime_pow, padicValNat_self]
    repeat rw [padicValNat.eq_zero_of_not_dvd (by norm_num)]