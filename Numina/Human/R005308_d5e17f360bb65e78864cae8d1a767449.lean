import Mathlib

namespace number_theory_607539

/- First obtain a more user-friendly version of Fermat's Little Theorem:
 If a, p ∈ ℕ, p is a prime, and a and p are coprime, then a^(p-1) ≡ 1 [MOD p]. -/
lemma fermatLittle {a p : ℕ} (hp : Nat.Prime p) (ha : a.Coprime p) : a^(p-1) ≡ 1 [MOD p] := by
  have : IsCoprime (a : ℤ) (p : ℤ) := by simpa[Int.coprime_iff_nat_coprime] using ha
  let fermat := @Int.ModEq.pow_card_sub_one_eq_one p hp a this
  rw [← Int.natCast_modEq_iff]
  ring_nf
  have : ∃ m : ℕ, p = m + 1 := by refine Nat.exists_eq_add_of_le' ?h; exact Nat.Prime.one_le hp
  obtain ⟨ m, hm ⟩ := this
  rw [hm] at fermat ⊢ 
  simp_all
  
/- Under the same assumptions on a and p as in the previous result,
the least d such that a^d ≡ 1 [MOD p] divides every n such that a^n ≡ 1 [MOD p]. -/
lemma fermatMin {a p : ℕ} (hp : Nat.Prime p) (ha : a.Coprime p) :
  ∃ d : ℕ, d ≥ 1 ∧ d ≤ p - 1 ∧ a^d ≡ 1 [MOD p] ∧
    (∀ n : ℕ, a^n ≡ 1 [MOD p] → d ∣ n) := by

  let s := (Finset.Icc 1 (p - 1)).filter (fun k ↦ a^k ≡ 1 [MOD p])

  have : s.Nonempty := by
    have : p - 1 ∈ s := by simp [s]
                           constructor
                           . have : 1 = 2 - 1 := by norm_num
                             nth_rewrite 1 [this]
                             rw [Nat.sub_le_sub_iff_right]
                             exact Nat.Prime.two_le hp
                             exact Nat.Prime.one_le hp
                           . apply fermatLittle hp ha
    use p-1

  obtain ⟨ d, hd ⟩ := Finset.min_of_nonempty this
  use d
  have : d ∈ s := by apply Finset.mem_of_min; exact hd

  rw [Finset.mem_filter] at this
  obtain ⟨ hl, hr ⟩ := this
  simp [Finset.mem_Ioc] at hl
  have ⟨ hll, hlr ⟩ := hl
  refine And.intro hll ?_
  refine And.intro hlr ?_
  refine And.intro hr ?_
  intro n hmodn
  rw [← Nat.mod_add_div n d, pow_add, pow_mul] at hmodn
  have : a ^ (n % d) * (a ^ d) ^ (n / d) ≡ a ^ (n % d) * 1 [MOD p] := by
    apply Nat.ModEq.mul_left
    apply Nat.ModEq.pow (n / d) at hr
    simp at hr
    exact hr
  by_cases hrem : n % d ≥ 1
  . have hnltmin : n % d < d := by apply Nat.mod_lt; exact hll
    have hrs : n % d ∈ s := by
      simp [s]
      constructor
      . refine And.intro hrem ?_
        linarith
      . obtain ggg := Nat.ModEq.trans (Nat.ModEq.symm this) hmodn
        simp at ggg
        exact ggg
    obtain hmin := Finset.min_le_of_eq hrs hd
    linarith
  . simp at hrem
    apply Nat.dvd_of_mod_eq_zero at hrem
    assumption

end number_theory_607539

open number_theory_607539

/-
Let n and m be natural numbers such that m ≥ 1 and m is odd.
Prove that 2 ^ m - 1 and 2 ^ n + 1 are coprime.
-/
theorem number_theory_607539 (m : ℕ) (hm : m ≥ 1) (hmOdd : Odd m) :Nat.Coprime (2 ^ m - 1) (2 ^ n + 1) := by

  -- We prove by contradiction
  by_contra h

  -- Let p be a prime that divides both 2 ^ m - 1 and 2 ^ n + 1.
  rw [Nat.Prime.not_coprime_iff_dvd] at h
  obtain ⟨ p, ⟨ hp, h1, h2⟩  ⟩ := h

  by_cases foo : p = 2
  . -- Suppose that p = 2

    -- Note that 2 ^ m - 1 is odd since m ≥ 1.
    have : Odd (2 ^ m - 1)  := by refine Nat.Even.sub_odd ?h ?hm ?hn
                                  . exact Nat.one_le_two_pow
                                  . refine (Nat.even_pow' ?hm.h).mpr ?hm.a
                                    . exact Nat.not_eq_zero_of_lt hm
                                    . exact Nat.even_iff.mpr rfl
                                  . exact Nat.odd_iff.mpr rfl
    -- But p = 2 and p divides 2 ^ m - 1 by assumption.
    -- Thus 2 ^ m - 1 is even.
    rw [foo] at h1
    have : Even (2 ^ m - 1) := by exact (even_iff_exists_two_nsmul (2 ^ m - 1)).mpr h1
    -- 2 ^ m - 1 cannot be both odd and even and we have a contradiction.
    rw [← Nat.not_odd_iff_even] at this
    contradiction
  . -- Suppose that p ≠ 2.
    -- Since p is prime, p and 2 are coprime.
    have : p.Coprime 2 := by refine Nat.coprime_two_right.mpr ?_; exact Nat.Prime.odd_of_ne_two hp foo

    -- Since p divides 2 ^ m - 1, we have 2 ^ m ≡ 1 [MOD p]
    have h3 : 2 ^ m ≡ 1 [MOD p] := by apply Nat.ModEq.symm
                                      rw [Nat.modEq_iff_dvd']
                                      exact h1
                                      exact Nat.one_le_two_pow

    -- Since p divides 2 ^ n + 1 and 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1),
    -- we have that p divides 2 ^ (2 * n) - 1 and so 2 ^ (2 * n) ≡ 1 [MOD p].
    have h4 : 2 ^ (2 * n) ≡ 1 [MOD p] := by
      suffices p ∣ 2 ^ (2 * n) - 1 by apply Nat.ModEq.symm
                                      rw [Nat.modEq_iff_dvd']
                                      exact this
                                      exact Nat.one_le_two_pow
      have : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        symm
        calc
          _ = 2 ^ n * (2 ^ n - 1) + (2 ^ n - 1) := by ring
          _ = 2 ^ n * (2 ^ n) - (2 ^ n * 1) + (2 ^ n - 1) := by rw [Nat.mul_sub]
          _ = 2 ^ n * (2 ^ n) - 2 ^ n + (2 ^ n - 1) := by rw [Nat.mul_one]
          _ = 2 ^ n * (2 ^ n) + (2 ^ n - 1) - 2 ^ n := by refine Eq.symm (Nat.sub_add_comm ?h)
                                                          exact Nat.le_mul_self (2 ^ n)
          _ = (2 ^ (2 * n)) + (2 ^ n - 1) - 2 ^ n := by ring_nf
          _ = (2 ^ (2 * n)) + 2 ^ n - 1 - 2 ^ n := by rw [← Nat.add_sub_assoc]
                                                      exact Nat.one_le_two_pow
          _ = (2 ^ (2 * n)) + 2 ^ n - 2 ^ n - 1 := by rw [Nat.sub_right_comm]
          _ = (2 ^ (2 * n)) + (2 ^ n - 2 ^ n) - 1 := by rw [Nat.add_sub_assoc Nat.le.refl (2 ^ (2 * n))]
          _ = (2 ^ (2 * n)) + 0 - 1 := by rw [Nat.sub_self]
          _ = (2 ^ (2 * n)) - 1 := by ring_nf
      rw [this]
      apply Dvd.dvd.mul_right h2

    -- Obtain w so that 1 ≤ w, w ≤ p - 1, 2 ^ w ≡ 1 [MOD p],
    -- and for all k such that 2 ^ k ≡ 1 [MOD p], we have w divides k.
    -- Since 2 ^ (2 * n) ≡ 1 [MOD p], we have that w divides 2 * n.
    obtain ⟨ w, hw ⟩ := fermatMin hp (Nat.coprime_comm.mp this)
    obtain ⟨ _, _, hwmod, hn ⟩ := hw

    -- It follows that w divides m.
    obtain hnm := hn m h3
    -- Since m is odd, we must have that w is odd.
    have : Odd w := by exact Odd.of_dvd_nat hmOdd hnm

    -- Thus w and 2 are coprime.
    -- Since w divides 2 * n, we have that w divides n.
    have : w.Coprime 2 := by exact Nat.coprime_two_right.mpr this
    have : w ∣ n := by exact Nat.Coprime.dvd_of_dvd_mul_left this (hn (2 * n) h4)

    -- Hence, there exists d such that n = w * d and so
    -- 2 ^ n = (2 ^ w) ^ d ≡ 1 ^ d ≡ 1 [MOD p].
    have : 2 ^ n ≡ 1 [MOD p] := by
      obtain ⟨ d, hd ⟩ := exists_eq_mul_left_of_dvd this
      rw [hd]
      calc
        _ = (2 ^ w) ^ d := by ring
        _ ≡ 1 ^ d [MOD p] := by exact Nat.ModEq.pow d hwmod
        _ = 1 := by ring


    -- Thus, p divides 2 ^ n - 1.
    have : p ∣ 2 ^ n - 1 := by refine (Nat.modEq_iff_dvd' ?h).mp (id (Nat.ModEq.symm this))

    -- Since p also divides 2 ^ n + 1, we have that p divides (2 ^ n + 1) + (2 ^ n - 1),
    -- implying that p divides 2 ^ (n + 1).
    have claim : p ∣ (2 ^ n + 1) + (2 ^ n - 1) := by exact (Nat.dvd_add_iff_right h2).mp this
    have : p ∣ 2 ^ (n + 1) := by
      have : (2 ^ n + 1) + (2 ^ n - 1) = 2 ^ (n + 1) := by
        calc
          _ = (2 ^ n + 1 + 2 ^ n) - 1 := by rw [← Nat.add_sub_assoc]
                                            exact Nat.one_le_two_pow
          _ = (2 ^ n + 2 ^ n + 1) - 1 := by ring_nf
          _ = 2 ^ n + 2 ^ n + (1 - 1) := by rw [Nat.add_succ_sub_one]
          _ = 2 ^ (n + 1) := by ring
      rw [← this]
      exact claim

    -- Since p is prime, we must have p divides 2, implying that p = 2.
    -- This is a contradiction.
    have hp2 : p ∣ 2 := by exact Nat.Prime.dvd_of_dvd_pow hp this
    apply foo
    rw [← Nat.prime_dvd_prime_iff_eq hp Nat.prime_two]
    exact hp2
