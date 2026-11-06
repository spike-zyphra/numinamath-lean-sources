import Mathlib

/- What is the greatest common divisor of all of the members of the set containing all numbers that are the product of four consecutive positive integers?-/
theorem number_theory_23051 : IsGreatest {d : ℕ | ∀ n : ℕ, 0 < n → d ∣ n * (n + 1) * (n + 2) * (n + 3)} 24 := by
  constructor
  . intro n _
    rw [Nat.dvd_iff_mod_eq_zero]
    change _ ≡ 0 [MOD 3 * 8]
    rw [← Nat.modEq_and_modEq_iff_modEq_mul (by norm_num)]
    constructor
    -- Similarly, one of the numbers will be $0\mod 3$,
    -- so the product will be divisible by 3.
    . have : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
      rw [Nat.ModEq]
      conv_lhs =>
        rw [Nat.mul_mod]
        lhs
        congr
        . rw [Nat.mul_mod]
          lhs
          congr
          . rw [Nat.mul_mod]
            lhs; rhs
            rw [Nat.add_mod]
          rw [Nat.add_mod]
        rw [Nat.add_mod]
      interval_cases n % 3
      all_goals norm_num
    -- These numbers are all in the form $n(n+1)(n+2)(n+3)\pmod 4$,
    -- there will be one number of each residue,
    -- so one of the numbers will be divisible by 2 and another divisible by 4,
    -- leaving the product divisible by 8.
    have : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
    rw [Nat.ModEq]
    conv_lhs =>
      rw [Nat.mul_mod]
      lhs
      congr
      . rw [Nat.mul_mod]
        lhs
        congr
        . rw [Nat.mul_mod]
          lhs; rhs
          rw [Nat.add_mod]
        rw [Nat.add_mod]
      rw [Nat.add_mod]
    interval_cases n % 8
    all_goals norm_num
  -- The GCD must therefore be divisible by $3\cdot8=24$.
  -- It also must be less than or equal to the smallest number in the set, $1\cdot2\cdot3\cdot4=24$,
  -- so it must be $\boxed{24}$ exactly.
  simp [upperBounds]
  intro a h
  specialize h 1 (by norm_num)
  apply Nat.le_of_dvd (by norm_num)
  exact h
