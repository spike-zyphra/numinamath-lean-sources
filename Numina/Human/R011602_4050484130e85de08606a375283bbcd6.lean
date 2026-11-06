import Mathlib

/- The sequence $a_{1}, a_{2}, \cdots$ is defined as follows:

$$

a_{n}=2^{n}+3^{n}+6^{n}-1(n=1,2,3, \cdots) .

$$


Find all positive integers that are coprime with every term of this sequence. -/
theorem number_theory_264384 {a : ℕ → ℤ}
    (ha : ∀ n, a n = 2 ^ n + 3 ^ n + 6 ^ n - 1) :
    {n | 0 < n ∧ ∀ m, IsCoprime n (a m)} = {1} := by
  -- convert the goal to an iff statement
  ext x
  simp
  constructor
  -- to prove x being coprime to all implies x = 1, we'll prove contrapositive that x > 1 then x is coprime to some element
  . contrapose
    simp
    rintro hx1 hx0
    -- there is a prime that divides x
    have hp : ∃ p, Nat.Prime p ∧ (p : ℤ) ∣ x := by
      lift x to ℕ using hx0.le
      norm_cast at hx1 ⊢
      apply Nat.exists_prime_and_dvd hx1
    obtain ⟨p, hp, hpx⟩ := hp
    -- it is enought to prove p is not coprime to a(n) for some n
    suffices ∃ n, ¬ IsCoprime (p : ℤ) (a n) by
      obtain ⟨n, h⟩ := this
      use n
      apply mt IsCoprime.of_isCoprime_of_dvd_left
      simp
      exact ⟨hpx, h⟩
    -- p is a prime as int, will be used later
    have hp' : Prime (p : ℤ) := by
      exact Nat.prime_iff_prime_int.mp hp
    -- convert the goal to prime dividing some a(n)
    simp_rw [Prime.coprime_iff_not_dvd hp']
    simp
    -- either p ≤ 3 or p > 3
    obtain hp_ub | hp_lb := le_or_gt p 3
    -- if p ≤ 3, do casework, rule out 0, 1 for 2 and 3 we have n = 1 an n = 2 as witness
    . interval_cases p
      any_goals norm_num at hp
      . use 1
        rw [ha]
        norm_num
      . use 2
        rw [ha]
        norm_num
    -- otherwise n = p-2 will be witness
    . use (p - 2)
      rw [ha]
      -- p is coprime to 2, 3, 6
      have hp2 : IsCoprime (p: ℤ) (2 : ℤ) := by
        rw [Prime.coprime_iff_not_dvd hp']
        norm_cast
        apply mt (Nat.le_of_dvd (by norm_num))
        omega
      have hp3 : IsCoprime (p: ℤ) (3 : ℤ) := by
        rw [Prime.coprime_iff_not_dvd hp']
        norm_cast
        apply mt (Nat.le_of_dvd (by norm_num))
        omega
      have hp6 : IsCoprime (p : ℤ) (6 : ℤ) := by
        rw [show (6 : ℤ) = 2 * 3 by norm_num]
        exact IsCoprime.mul_right hp2 hp3
      -- it suffices to prove p divides the 6 * term as coprime to 6, convert it to equation of ZMod
      suffices (p : ℤ) ∣ 6 * (2 ^ (p - 2) + 3 ^ (p - 2) + 6 ^ (p - 2) - 1) by
        apply IsCoprime.dvd_of_dvd_mul_left hp6 this
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      -- 2^(p-1), 3^(p-1), 6^(p-1) is 1 due to coprimeness
      have hp2' : (2 : ZMod p) ^ (p - 1) = 1 := by
        have : Nat.Coprime p 2 := by
          rw [show (2 : ℤ) = ↑(2 : ℕ) by norm_cast] at hp2
          exact hp2.nat_coprime
        have := congrArg Units.val (ZMod.units_pow_card_sub_one_eq_one p (ZMod.unitOfCoprime 2 this.symm))
        simpa using this
      have hp3' : (3 : ZMod p) ^ (p - 1) = 1 := by
        have : Nat.Coprime p 3 := by
          rw [show (3 : ℤ) = ↑(3 : ℕ) by norm_cast] at hp3
          exact hp3.nat_coprime
        have := congrArg Units.val (ZMod.units_pow_card_sub_one_eq_one p (ZMod.unitOfCoprime 3 this.symm))
        simpa using this
      have hp6' : (6 : ZMod p) ^ (p - 1) = 1 := by
        rw [show (6 : ZMod p) = 2 * 3 by norm_num]
        rw [mul_pow, hp2', hp3']
        norm_num
      -- now plug in the value and evaluate to show the result
      convert_to (3 : ZMod p) * 2 ^ (p-2 + 1) + 2 * 3 ^ (p-2 + 1) + 6 ^ (p-2 + 1) - 6 = 0
      . ring
      rw [show p - 2 + 1 = p - 1 by omega, hp2', hp3', hp6']
      norm_num
  -- for 1, it is coprime to all
  . rintro h
    rw [h]
    simp
    rintro n
    exact isCoprime_one_left