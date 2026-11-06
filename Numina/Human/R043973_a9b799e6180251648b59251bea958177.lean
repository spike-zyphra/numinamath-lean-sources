import Mathlib

theorem number_theory_7894 (a m n : ℕ) (agt : 1 < a)
    (mpos : 0 < m) (npos : 0 < n) :
    Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ (Nat.gcd m n) - 1 := by
  by_cases h : m = n; simp [h]
  wlog nltm : n < m
  · rw [Nat.gcd_comm]; nth_rw 2 [Nat.gcd_comm]
    apply this; any_goals assumption
    exact fun a => h (id (Eq.symm a)); omega
  set M' := m ⊔ n with hM; have hM1 : m ≤ M' := by simp [M']
  have hM2 : n ≤ M' := by simp [M']
  generalize M' = M at hM1 hM2; clear M' hM h; revert m n
  induction M using Nat.strong_induction_on with
  | h M ihM =>
    intro m n mpos npos mltn hM1 hM2
    rw [← Nat.gcd_sub_self_left, Nat.sub_sub_sub_cancel_right]
    rw [show m = m-n+n by omega, pow_add, ← Nat.sub_one_mul]
    rw [Nat.Coprime.gcd_mul_right_cancel, Nat.gcd_add_self_left]
    by_cases h : m - n = n; simp [h]
    rw [← ne_eq, Nat.ne_iff_lt_or_gt] at h; rcases h with h|h
    · rw [Nat.gcd_comm]; nth_rw 2 [Nat.gcd_comm]
      apply ihM (M-1); all_goals omega
    apply ihM (M-1); any_goals omega
    · nth_rw 1 [show a^n = a^n-1+1 by rw [Nat.sub_add_cancel]; apply Nat.one_le_pow; omega]
      simp [Nat.coprime_self_add_left]
    apply Nat.one_le_pow; omega
    gcongr; omega