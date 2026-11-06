import Mathlib

/- Find all primes  $p$  such that  $p+2$  and  $p^2+2p-8$  are also primes.-/
theorem number_theory_8800 {p : ℕ} (hpp : p.Prime) : (p + 2).Prime ∧ (p^2+2*p-8).Prime ↔
    p = 3 := by
  constructor
  swap
  -- Verify that p = 3 is solution.
  . rintro ⟨rfl⟩
    constructor <;> norm_num
  rintro ⟨hpadd2, hp⟩
  have hpmod3 : p ≡ (p % 3) [MOD 3] := by
    exact Nat.ModEq.symm (Nat.mod_modEq p 3)
  have hp_add2_mod3 : p + 2 ≡ (p + 2) % 3 [MOD 3] := by
    exact Nat.ModEq.symm (Nat.mod_modEq (p + 2) 3)
  rw [Nat.add_mod] at hp_add2_mod3
  have : p ^ 2 + 2 * p - 8 > 0 := by
    by_contra h
    push_neg at h
    norm_num [show p ^ 2 + 2 * p - 8 = 0 by omega] at hp
  have : p ^ 2 + 2 * p - 8 + 9 = p ^ 2 + 2 * p + 1 := by omega
  have h9mod3 : 9 ≡ 0 [MOD 3] := rfl
  have h1 := (Nat.ModEq.refl (p ^  2 + 2 * p - 8)).add h9mod3
  symm at h1
  rw [Nat.add_zero, this, Nat.ModEq, Nat.add_mod, Nat.add_mod (p ^ 2), Nat.pow_mod, Nat.mul_mod] at h1
  have : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases p % 3
  -- hence,  $p \equiv 0\pmod{3}$ , but the only prime, is  $3$ , and  $3$ , works.
  . rw [Nat.modEq_zero_iff_dvd, Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp] at hpmod3
    exact hpmod3.symm
  -- If  $p \equiv 1\pmod{3}$ , then,  $p+2$ , is not prime.
  . norm_num at hp_add2_mod3
    rw [Nat.modEq_zero_iff_dvd, Nat.prime_dvd_prime_iff_eq Nat.prime_three hpadd2] at hp_add2_mod3
    norm_num [show p = 1 by omega] at hpp
  -- If  $p \equiv 2\pmod{3}$ , then  $p^2+2p-8$ , is divisible by  $3$ ,
  . norm_num at h1
    rw [← Nat.dvd_iff_mod_eq_zero, Nat.prime_dvd_prime_iff_eq Nat.prime_three hp] at h1
    by_cases hpgt : 3 < p
    . have : 7 < p ^ 2 + 2 * p - 8 := by nlinarith
      norm_num [← h1] at this
    have : 2 ≤ p := Nat.Prime.two_le hpp
    interval_cases p
    all_goals norm_num at h1
