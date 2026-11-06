import Mathlib

theorem number_theory_299063 : 2003^2004^2005^2008 ≡ 1 [MOD 80] := by
  apply Nat.ModEq.trans (Nat.ModEq.pow _ (show 2003 ≡ 3 [MOD 80] by native_decide))
  have : ∀n, 3^n ≡ 1 [MOD 80] ↔ n ≡ 0 [MOD 4] := by
    intro n
    obtain ⟨k, r, hn, hr⟩ := show ∃k r, n = 4 * k + r ∧ r < 4 by
      use n / 4, n % 4
      omega
    rw [Nat.ModEq, Nat.ModEq, show n % 4 = r by omega, hn, pow_add]
    rw [Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
    interval_cases r <;> norm_num
  rw [this]
  apply Nat.ModEq.trans (Nat.ModEq.pow _ (show 2004 ≡ 0 [MOD 4] by native_decide))
  rw [zero_pow]
  intro h
  linarith [pow_eq_zero h]
