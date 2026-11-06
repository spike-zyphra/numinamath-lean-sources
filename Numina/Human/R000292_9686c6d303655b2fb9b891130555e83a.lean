import Mathlib

/- Find all positive integers  $m$  and  $n$  such that  $1 + 5 \cdot 2^m = n^2$ .-/
theorem number_theory_8836 {m n : ℤ} (hmpos : 0 < m) (hnpos : 0 < n) :
    1 + 5 * 2 ^ m.natAbs = n ^ 2 ↔ m = 4 ∧ n = 9 := by
  have hprime5 : Nat.Prime 5 := by norm_num
  constructor
  swap
  -- Verify that m=4,n=9 is solution.
  . rintro ⟨rfl, rfl⟩
    norm_num
  intro hmn
  replace hmn : (n + 1) * (n - 1) = 5 * 2 ^ m.natAbs := by linear_combination -hmn
  have h5dvd : 5 ∣ (n + 1) * (n - 1) := by use 2 ^ m.natAbs
  -- We know that either 5 divides n+1 or 5 divides n-1 from 1+5*2^m=n^2
  replace h5dvd : 5 ∣ n + 1 ∨ 5 ∣ n - 1 := by
    rw [← Nat.cast_ofNat]
    apply Int.Prime.dvd_mul' hprime5
    rw [Nat.cast_ofNat]
    exact h5dvd
  rcases h5dvd with ⟨k, hk⟩ | ⟨k, hk⟩
  -- Case 1:  $n-1=2^p$
  . rw [hk, mul_assoc, mul_right_inj' (by norm_num)] at hmn
    have hn_sub_one_dvd : n - 1 ∣ 2 ^ m.natAbs := by use k; linear_combination -hmn
    have hk_dvd : k ∣ 2 ^ m.natAbs := by use n - 1; linear_combination -hmn
    have : (n - 1).natAbs ∣ 2 ^ m.natAbs ∧ k.natAbs ∣ 2 ^ m.natAbs := by
      zify
      repeat rw [abs_dvd]
      constructor <;> assumption
    repeat rw [Nat.dvd_prime_pow Nat.prime_two] at this
    rcases this with ⟨⟨p, hple, hp⟩, ⟨q, hqle, hq⟩⟩
    zify at hp hq
    rw [abs_of_nonneg (by omega)] at hp hq
    rw [show n + 1 = 2 ^ p + 2 by omega, hq] at hk
    rcases le_or_lt q 0 with hq0 | hq0
    -- If q = 0 then 2^p = 3 which is contradictory.
    . replace hq0 : q = 0 := Nat.le_antisymm hq0 (Nat.zero_le _)
      rw [hq0, pow_zero, mul_one] at hk
      replace hk : 2 ^ p = (3 : ℤ) := by omega
      rcases le_or_lt p 0 with hp0 | hp0
      . replace hp0 : p = 0 := Nat.le_antisymm hp0 (Nat.zero_le _)
        norm_num [hp0] at hk
      . apply_fun (· % 2) at hk
        rw [show p = p - 1 + 1 by omega, pow_succ, Int.mul_emod, Int.emod_self] at hk
        norm_num at hk
    -- If p = 0 then 5*2^q = 3 which is contradictory.
    have hppos : 0 < p := by
      rw [Nat.pos_iff_ne_zero]
      intro hp0
      apply_fun (· % 2) at hk
      rw [hp0, show q = q - 1 + 1 by omega, Int.mul_emod, pow_succ, Int.mul_emod _ 2, Int.emod_self] at hk
      norm_num at hk
    rw [show p = p - 1 + 1 by omega, show q = q - 1 + 1 by omega, pow_succ, pow_succ, ← mul_assoc] at hk
    conv at hk => lhs; rhs; rw [← one_mul 2]
    rw [← add_mul, mul_left_inj' (by norm_num)] at hk
    change 1 ≤ _ at hq0 hppos
    rcases le_or_lt q 1 with hq1 | hq1
    -- Since  $2^{p-1}$  is odd, we know that  $p=3$  and  $m=4$ .
    -- Then, we have  $n=9$ , so  $(m,n)=(4,9)$  is a solution.
    . replace hq1 : q = 1 := Nat.le_antisymm hq1 hq0
      rw [hq1] at hk
      norm_num at hk
      have : 2 ^ (p - 1) = (2 : ℤ) ^ 2 := by omega
      have := Int.pow_right_injective (by norm_num) this
      have hp3 : p = 3 := by omega
      rw [hp3] at hp
      rw [hq1] at hq
      rw [hp, hq, ← pow_add] at hmn
      have hm := Int.pow_right_injective (by norm_num) hmn
      constructor <;> omega
    have hpgt1 : 1 < p := by
      by_contra h
      push_neg at h
      interval_cases p
      norm_num at hk
      have : 2 < (2 : ℤ) := by
        nth_rw 2 [hk]
        omega
      linarith
    apply_fun (· % 2) at hk
    rw [show p - 1 = p - 2 + 1 by omega, show q - 1 = q - 2 + 1 by omega, pow_succ, pow_succ,
      Int.add_emod, Int.mul_emod, Int.mul_emod 5, Int.mul_emod _ 2, Int.emod_self] at hk
    norm_num at hk
  -- Case 2:  $n+1=2^p$ Similarly to case 1
  . rw [hk, mul_comm, mul_assoc, mul_right_inj' (by norm_num)] at hmn
    have hn_add_one_dvd : n + 1 ∣ 2 ^ m.natAbs := by use k; linear_combination -hmn
    have hk_dvd : k ∣ 2 ^ m.natAbs := by use n + 1; linear_combination -hmn
    have : (n + 1).natAbs ∣ 2 ^ m.natAbs ∧ k.natAbs ∣ 2 ^ m.natAbs := by
      zify
      repeat rw [abs_dvd]
      constructor <;> assumption
    repeat rw [Nat.dvd_prime_pow Nat.prime_two] at this
    rcases this with ⟨⟨p, hple, hp⟩, ⟨q, hqle, hq⟩⟩
    zify at hp hq
    rw [abs_of_nonneg (by omega)] at hp hq
    rw [show n - 1 = 2 ^ p - 2 by omega, hq] at hk
    rcases le_or_lt q 0 with hq0 | hq0
    . replace hq0 : q = 0 := Nat.le_antisymm hq0 (Nat.zero_le _)
      rw [hq0, pow_zero, mul_one] at hk
      replace hk : 2 ^ p = (7 : ℤ) := by omega
      rcases le_or_lt p 0 with hp0 | hp0
      replace hp0 : p = 0 := Nat.le_antisymm hp0 (Nat.zero_le _)
      norm_num [hp0] at hk
      apply_fun (· % 2) at hk
      rw [show p = p - 1 + 1 by omega, pow_succ, Int.mul_emod, Int.emod_self] at hk
      norm_num at hk
    have hppos : 0 < p := by
      rw [Nat.pos_iff_ne_zero]
      intro hp0
      apply_fun (· % 2) at hk
      rw [hp0, show q = q - 1 + 1 by omega, Int.mul_emod, pow_succ, Int.mul_emod _ 2, Int.emod_self] at hk
      norm_num at hk
    rw [show p = p - 1 + 1 by omega, show q = q - 1 + 1 by omega, pow_succ, pow_succ, ← mul_assoc] at hk
    conv at hk => lhs; rhs; rw [← one_mul 2]
    rw [← sub_mul, mul_left_inj' (by norm_num)] at hk
    change 1 ≤ _ at hq0 hppos
    rcases le_or_lt q 1 with hq1 | hq1
    -- we get  $2^p-1=5$ , which yields no integer solution.
    . replace hq1 : q = 1 := Nat.le_antisymm hq1 hq0
      rw [hq1] at hk
      norm_num at hk
      have : p ≠ 0 := fun h => by norm_num [h] at hk
      replace hk : 2 ^ (p - 1) = (2 : ℤ) * 3 := by omega
      have : 3 ∣ 2 ^ (p - 1) := by
        zify
        use 2
        linear_combination hk
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
      norm_num at this
    have hpgt1 : 1 < p := by
      by_contra h
      push_neg at h
      interval_cases p
      norm_num at hk
    apply_fun (· % 2) at hk
    rw [show p - 1 = p - 2 + 1 by omega, show q - 1 = q - 2 + 1 by omega, pow_succ, pow_succ,
      Int.sub_emod, Int.mul_emod, Int.mul_emod 5, Int.mul_emod _ 2, Int.emod_self] at hk
    norm_num at hk
