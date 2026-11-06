import Mathlib

/- IMO 1978 Problem A1 m and n are positive integers with m < n. The last three decimal digits of 1978 m are the same as the last three decimal digits of 1978 n . Find m and n such that m + n has the least possible value. -/
theorem number_theory_143259 :
    IsLeast {x | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m < n ∧ (1978 ^ m) % 1000 = (1978 ^ n) % 1000 ∧ x = m + n} (3 + 103) := by
  -- Show that 1978 ^ 3 % 1000 = 1978 ^ 103 % 1000 and that
  -- the assumption 1978 ^ m % 1000 = 1978 ^ n % 1000 implies 106 ≤ m + n.
  simp only [IsLeast, gt_iff_lt, Nat.reduceAdd, Set.mem_setOf_eq, lowerBounds,
    forall_exists_index, and_imp]
  constructor
  -- Check that 1978 ^ 3 % 1000 = 1978 ^ 103 % 1000.
  · use 3, 103
    norm_num
  -- Assume that 0 < m < n and 1978 ^ m % 1000 = 1978 ^ n % 1000.
  -- We need to show that 106 ≤ m + n.
  intro s m n hm0 hn0 hmn heq hsmn
  -- We have 1978 ^ m ≤ 1978 ^ n since m < n.
  have ineq : 1978 ^ m ≤ 1978 ^ n := Nat.pow_le_pow_right (by norm_num) (le_of_lt hmn)
  -- 1978 ^ m % 1000 = 1978 ^ n % 1000 implies that 1000 ∣ 1978 ^ n - 1978 ^ m.
  rw [← Nat.ModEq.eq_1, Nat.modEq_iff_dvd' ineq] at heq
  -- Let d = n - m > 0.
  set d := n - m
  -- We have 1978 ^ n - 1978 ^ m = 1978 ^ m * (1978 ^ d - 1).
  have eq : 1978 ^ n - 1978 ^ m = 1978 ^ m * (1978 ^ d - 1) := by
    rw [Nat.mul_sub, ← Nat.pow_add, show m + d = n by omega, mul_one]
  -- It is enough to show that 3 ≤ m and 100 ≤ d = n - m.
  suffices 3 ≤ m ∧ 100 ≤ d by omega
  constructor
  -- Show that 3 ≤ m.
  -- Prove that 8 ∣ 1978 ^ m.
  · have h : 8 ∣ 1978 ^ m := by
      -- 8 = 2 ^ 3 and 1978 ^ d - 1 are coprime.
      have hp : Nat.Coprime (2 ^ 3) (1978 ^ d - 1) := by
        -- It is enough to show that 2 and 1978 ^ d - 1 are coprime.
        apply Nat.Coprime.pow_left
        apply IsCoprime.nat_coprime
        dsimp [IsCoprime]
        push_cast [show 1 ≤ 1978 ^ d by exact Nat.one_le_pow' d 1977]
        -- Find a and b such that a * 2 + b * (1978 ^ d - 1) = 1.
        -- Take a = 2 ^ (d - 1) * 989 ^ d and b = -1.
        use 2 ^ (d - 1) * 989 ^ d, -1
        rw [Int.mul_right_comm, ← Int.pow_succ, show d - 1 + 1 = d by omega, ← mul_pow]
        ring
      -- 8 and 1978 ^ d - 1 are coprime so 8 * 125 = 1000 ∣ 1978 ^ m * (1978 ^ d - 1) implies
      -- that 8 ∣ 1978 ^ m.
      apply hp.dvd_of_dvd_mul_left
      trans 1000
      norm_num
      rwa [mul_comm, ← eq]
    -- Consider 3 cases: m = 1, m = 2, and 3 ≤ m.
    rcases show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega with hm | hm | hm
    -- If m = 1 then 8 does not divide 1978 ^ 1.
    · rw [hm] at h; norm_num at h
    -- If m = 2 then 8 does not divide 1978 ^ 2.
    · rw [hm] at h; norm_num at h
    -- We conclude that 3 ≤ m.
    · exact hm
  -- Show that 100 ≤ d.
  -- Prove that 125 divides 1978 ^ d - 1.
  have h : 125 ∣ 1978 ^ d - 1 := by
    -- Show that 125 and 1978 ^ m are coprime.
    have hp : Nat.Coprime 125 (1978 ^ m) := by
      apply Nat.Coprime.pow_right
      norm_num
    -- 125 and 1978 ^ m are coprime so 8 * 125 = 1000 ∣ 1978 ^ m * (1978 ^ d - 1) implies
    -- that 125 ∣ 1978 ^ d - 1.
    apply hp.dvd_of_dvd_mul_left
    trans 1000
    norm_num
    rwa [← eq]
  -- We have 1978 ^ d = 1 in ℤ_{125}.
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at h
  push_cast [show 1 ≤ 1978 ^ d from Nat.one_le_pow' _ _] at h
  -- 1978 and 125 are coprime so 1978 is a unit in ℤ_{125}.
  have hp : Nat.Coprime 1978 125 := by norm_num
  have hu := (ZMod.isUnit_iff_coprime 1978 125).mpr hp
  -- Show that the order of 1978 in ℤ_{125} divides d.
  -- It follows from 1978 ^ d = 1 in ℤ_{125}.
  have hd : orderOf hu.unit ∣ d := by
    simp [← orderOf_units]
    apply orderOf_dvd_of_pow_eq_one
    linear_combination h
  -- Show that the order of 1978 in ℤ_{125} divides 100.
  have hd100 : orderOf hu.unit ∣ 100 := by
    -- We have 100 = τ(125) (the totient of 125).
    rw [← show (125).totient = 100 by decide]
    -- The order of any unit in ℤ_{125} divides the totient.
    apply orderOf_dvd_of_pow_eq_one
    exact ZMod.pow_totient _
  simp [← orderOf_units] at hd100 hd
  -- 1978 ^ orderOf 1978 = 1 in ℤ_{125}.
  have hpow := pow_orderOf_eq_one (1978 : ZMod 125)
  -- Let k = orderOf 1978 in ℤ_{125}.
  set k := orderOf (1978 : ZMod 125)
  -- Show that 100 ≤ k.
  suffices 100 ≤ k by
    apply Nat.le_of_dvd (by omega) at hd
    linarith
  -- We proved that k is a divisor of 100 so k ∈ {1, 2, 4, 5, 10, 20, 25, 50, 100}.
  have hk : k ∈ ({1, 2, 4, 5, 10, 20, 25, 50, 100} : Finset ℕ) := by
    rw [← show (100).divisors = {1, 2, 4, 5, 10, 20, 25, 50, 100} from rfl]
    simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true, hd100]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  -- 1978 ^ k = 1 in ℤ_{125} implies that 1978 ^ k % 125 = 1.
  replace hpow : 1978 ^ k % 125 = 1 := by
    rw [show 1 = ((1 : ℕ) : ZMod 125) by rfl] at hpow
    rw [show 1978 ^ k = ((1978 ^ k : ℕ) : ZMod 125) by simp] at hpow
    rw [ZMod.natCast_eq_natCast_iff'] at hpow
    simp [hpow]
  -- Consider all possible values of k and find out that only k = 100 yields 1978 ^ k % 125 = 1.
  rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk <;> rw [hk] at hpow <;> norm_num at hpow
  rw [hk]