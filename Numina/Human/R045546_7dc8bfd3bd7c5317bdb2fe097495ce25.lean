import Mathlib


namespace number_theory_609540

/- First obtain a more user-friendly version of Fermat's Little Theorem:
 If a, p ∈ ℕ, p is a prime, and a and p are coprime, then a^(p-1) ≡ 1 [MOD p]. -/
lemma fermatLittle {a p : ℕ} (hp : Nat.Prime p) (ha : a.Coprime p) : a^(p-1) ≡ 1 [MOD p] := by
  have : IsCoprime (a : ℤ) (p : ℤ) := by simp [Int.coprime_iff_nat_coprime]
                                         exact ha

  let fermat := @Int.ModEq.pow_card_sub_one_eq_one p hp a this
  rw [← Int.natCast_modEq_iff]
  ring_nf
  have : ∃ m : ℕ, p = m + 1 := by refine Nat.exists_eq_add_of_le' ?h; exact Nat.Prime.one_le hp
  obtain ⟨ m, hm ⟩ := this
  rw [hm]
  rw [hm] at fermat
  simp at *
  exact fermat

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

end number_theory_609540

open number_theory_609540

/- Determine the number of integers $2 \leq n \leq 2016$ such that $n^{n}-1$ is divisible by $2,3,5,7$.-/
theorem number_theory_609540 (s : Finset ℕ) :
  s = (Finset.Icc 2 2016).filter (fun n : ℕ ↦ ∀ p ∈ [2,3,5,7], n^n ≡ 1 [MOD p]) → s.card = 9 := by

  intro h

  let f : ℕ ↪ ℕ :=
    {
      toFun := fun k ↦ 210 * (k + 1) + 1
      inj' := by intro x y; simp
    }

  -- It suffices to show that s is equal to { 210*(k+1)+1 | k = 0,...,8 }
  suffices s = (Finset.range 9).map f by rw [this]; simp

  apply Finset.ext
  intro a
  simp [f, h]

  -- If n, p ∈ ℕ and p is prime, then n ≡ 1 [MOD p] implies n^n ≡ 1 [MOD p]
  have claim1 {n p : ℕ} (hp : Nat.Prime p) : n ≡ 1 [MOD p] → n^n ≡ 1 [MOD p] := by
    intro h
    apply Nat.ModEq.pow n at h
    simp at h
    assumption

  constructor
  . -- Show the forward direction
    intro ha
    obtain ⟨ ⟨ halb, haub⟩, hamod ⟩ := ha
    obtain prime2 := Nat.prime_two
    obtain prime3 := Nat.prime_three
    obtain prime5 := Nat.prime_five
    have prime7 : Nat.Prime 7 := by decide

    -- a is coprime with each of the primes 2, 3, 5, 7
    have claimCoprime : (∀ p ∈ [2,3,5,7], a.Coprime p) := by
      rcases hamod with ⟨ mod2, mod3, mod5, mod7 ⟩
      simp
      have h' (p : ℕ) (hp' : Nat.Prime p): a ^ a ≡ 1 [MOD p] → a.Coprime p := by
        by_contra g
        push_neg at g
        obtain ⟨ gmod, gcoprime ⟩ := g
        have azero : a ≡ 0 [MOD p] := by
          obtain hh := @Nat.Prime.dvd_iff_not_coprime p a hp'
          rw [Nat.coprime_comm] at gcoprime
          rw [← hh] at gcoprime
          exact Nat.modEq_zero_iff_dvd.mpr gcoprime
        have : a^a ≡ 0 [MOD p] := by
          calc
            _ ≡ 0^a [MOD p] := Nat.ModEq.pow a azero
            _ = 0 := by apply Nat.zero_pow; linarith
        ring_nf at this
        apply Nat.ModEq.symm at this
        have : 0 ≡ 1 [MOD p] := by exact Nat.ModEq.trans this gmod
        simp at this
        apply Nat.ModEq.dvd at this
        ring_nf at this
        norm_cast at this
        revert this
        simp
        exact Nat.Prime.ne_one hp'
      constructor
      . obtain cor2 := h' 2 prime2 mod2
        simp at cor2
        exact cor2
      . exact ⟨h' 3 prime3 mod3, h' 5 prime5 mod5, h' 7 prime7 mod7 ⟩
    simp at claimCoprime
    obtain ⟨ cp2, cp3, cp5, cp7 ⟩ := claimCoprime
    obtain q2 := claim1 prime2
    obtain q3 := claim1 prime3
    obtain q5 := claim1 prime5
    obtain q7 := claim1 prime7

    -- a ^ a ≡ [MOD 2] if and only if a ≡ 1 [MOD 2]
    have p2 : a ^ a ≡ 1 [MOD 2] ↔ a ≡ 1 [MOD 2] := by
      constructor
      . intro
        apply Nat.modEq_of_dvd
        have : Odd (a : ℤ) := by refine (Int.odd_coe_nat a).mpr ?_; exact cp2
        rcases this with ⟨ k, hk ⟩
        rw [hk]
        simp
      . exact q2

    -- a ^ a ≡ [MOD 7] if and only if a ≡ 1 [MOD 7]
    have p7 : a ^ a ≡ 1 [MOD 7] ↔ a ≡ 1 [MOD 7] := by
      constructor
      . obtain fm := fermatMin prime7 cp7
        obtain ⟨ d, ⟨ dlb, dub, hdp, hd⟩  ⟩ := fm
        obtain hda := hd a
        obtain hd7 := hd (7 - 1) (fermatLittle prime7 cp7)
        simp at hd7
        have : d = 6 ∨ d = 3 ∨ d = 2 ∨ d = 1 := by
          let divisors_of_6 := Nat.divisors 6
          have : d ∈ divisors_of_6 := by
            rw [Nat.mem_divisors]
            apply And.intro
            . exact hd7
            . simp
          have dd6 : divisors_of_6 = {1, 2, 3, 6} := by exact rfl
          rw [dd6] at this
          simp at this
          omega
        rcases this with g | g
        . rw [g] at hda
          intro aa
          obtain a6 := hda aa
          rcases a6 with ⟨ k, hk ⟩
          have : 6 * k = 2 * (3 * k) := by ring
          rw [this] at hk
          have : Even a := by rw [Nat.even_iff, hk]; exact Nat.mul_mod_right 2 (3 * k)
          rw [← Nat.not_odd_iff_even] at this
          contradiction
        . rcases g with g' | g'
          . rw [g'] at hda
            intro aa
            obtain a3 := hda aa
            rw [Nat.coprime_comm] at cp3
            rw [Nat.Prime.coprime_iff_not_dvd _] at cp3
            contradiction
            exact Nat.prime_three
          . rcases g' with g'' | g''
            . rw [g''] at hda
              intro aa
              have : Even a := by exact (even_iff_exists_two_nsmul a).mpr (hda aa)
              rw [← Nat.not_odd_iff_even] at this
              contradiction
            . simp [g''] at hdp
              exact fun _ => hdp
      . have : Nat.Prime 7 := by decide
        exact q7

    -- a ^ a ≡ [MOD 5] if and only if a ≡ 1 [MOD 5]
    have p5 : a ^ a ≡ 1 [MOD 5] ↔ a ≡ 1 [MOD 5] := by
      constructor
      . obtain fm := fermatMin prime5 cp5
        obtain ⟨ d, ⟨ dlb, dub, hdp, hd⟩  ⟩ := fm
        obtain hda := hd a
        obtain hd5 := hd (5 - 1) (fermatLittle prime5 cp5)
        simp at hd5
        have : d = 4 ∨ d = 2 ∨ d = 1 := by
          let divisors_of_4 := Nat.divisors 4
          have : d ∈ divisors_of_4 := by
            rw [Nat.mem_divisors]
            apply And.intro
            . exact hd5
            . simp
          have dd4 : divisors_of_4 = {1, 2, 4} := by exact rfl
          rw [dd4] at this
          simp at this
          omega
        rcases this with g | g
        . rw [g] at hda
          intro aa
          obtain a4 := hda aa
          rcases a4 with ⟨ k, hk ⟩
          have : 4 * k = 2 * (2 * k) := by ring
          rw [this] at hk
          have : Even a := by rw [Nat.even_iff, hk]; exact Nat.mul_mod_right 2 (2 * k)
          rw [← Nat.not_odd_iff_even] at this
          contradiction
        . rcases g with g' | g'
          . rw [g'] at hda
            intro aa
            have : Even a := by rw [Nat.even_iff]; exact Nat.dvd_iff_mod_eq_zero.mp (hda aa)
            rw [← Nat.not_odd_iff_even] at this
            contradiction
          . simp [g'] at hdp
            exact fun _ => hdp
      . exact q5

    -- a ^ a ≡ [MOD 3] if and only if a ≡ 1 [MOD 3]
    have p3 : a ^ a ≡ 1 [MOD 3] ↔ a ≡ 1 [MOD 3] := by
      constructor
      . obtain fm := fermatMin prime3 cp3
        obtain ⟨ d, ⟨ dlb, dub, hdp, hd⟩  ⟩ := fm
        obtain hda := hd a
        obtain hd3 := hd (3 - 1) (fermatLittle prime3 cp3)
        simp at hd3
        have : d = 2 ∨ d = 1 := by
          let divisors_of_2 := Nat.divisors 2
          have : d ∈ divisors_of_2 := by
            rw [Nat.mem_divisors]
            apply And.intro
            . exact hd3
            . simp
          have dd2 : divisors_of_2 = {1, 2} := by exact rfl
          rw [dd2] at this
          simp at this
          omega
        rcases this with g | g
        . rw [g] at hda
          intro aa
          obtain a2 := hda aa
          have : Even a := by rw [Nat.even_iff]; exact Nat.dvd_iff_mod_eq_zero.mp (hda aa)
          rw [← Nat.not_odd_iff_even] at this
          contradiction
        . simp [g] at hdp
          exact fun a => hdp
      . exact q3

    -- Since 2, 3, 5, and 7 are primes, it follows that a ^ a ≡ [MOD p] for all p = 2, 3, 5, 7
    -- if and only if a ≡ 1 [MOD 210].
    have claim : (∀ p ∈ [2,3,5,7], a^a ≡ 1 [MOD p]) ↔ a ≡ 1 [MOD 210] := by
      simp
      have : 210 = 2 * (3 * (5 * 7)) := by norm_num
      rw [this]
      constructor
      . intro h'
        rw [p2, p3, p5, p7] at *
        repeat rw [← Nat.modEq_and_modEq_iff_modEq_mul]
        exact h'
        repeat decide
      . intro h'
        rw [p2, p3, p5, p7]
        repeat rw [← Nat.modEq_and_modEq_iff_modEq_mul] at h'
        exact h'
        repeat decide

    -- Rewrite the claim into a more convenient form.
    simp at claim
    simp [claim] at hamod
    revert hamod
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']
    intro ha
    obtain ⟨ k, hk ⟩ := ha
    -- Show that a must have the form 210 * k + 1 for a positive integer k.
    have : a = 210 * k + 1 := by refine Nat.eq_add_of_sub_eq ?hle hk; linarith
    use (k-1)
    rw [this] at haub halb

    -- Show that (k - 1) is in the range 0,...,8
    apply Nat.le_sub_one_of_lt at haub
    simp at haub
    constructor
    . omega
    . omega
    linarith

  . -- Show the backward direction
    intro ha
    obtain ⟨ k, ⟨ hklb, hkeq⟩  ⟩ := ha
    have : 2 ≤ a := by omega
    have claim2 {x : ℕ } : x + 1 - 1 = x := by exact rfl

    constructor
    . -- If a = 210 * (k + 1) + 1 for k = 0,...,8, then 2 ≤ a and a ≤ 2016
      omega
    . constructor
      . -- a ^ a ≡ 1 [MOD 2]
        apply claim1;
        decide
        rw [← hkeq]
        rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']
        have : 210 * (k + 1) + 1 - 1 = 2*(105*(k+1)) := by
          calc
            _ = 210 * (k + 1) := by apply claim2
            _ = _ := by ring
        rw [this]
        exact Nat.dvd_mul_right 2 (105 * (k + 1))
        simp
      . constructor
        . -- a ^ a ≡ 1 [MOD 3]
          apply claim1;
          decide
          rw [← hkeq]
          rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']
          have : 210 * (k + 1) + 1 - 1 = 3*(70*(k+1)) := by
            calc
              _ = 210 * (k + 1) := by apply claim2
              _ = _ := by ring
          rw [this]
          exact Nat.dvd_mul_right 3 (70 * (k + 1))
          simp
        . constructor
          . -- a ^ a ≡ 1 [MOD 5]
            apply claim1;
            decide
            rw [← hkeq]
            rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']
            have : 210 * (k + 1) + 1 - 1 = 5*(42*(k+1)) := by
              calc
                _ = 210 * (k + 1) := by apply claim2
                _ = _ := by ring
            rw [this]
            exact Nat.dvd_mul_right 5 (42 * (k + 1))
            simp
          . -- a ^ a ≡ 1 [MOD 7]
            apply claim1;
            decide
            rw [← hkeq]
            rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']
            have : 210 * (k + 1) + 1 - 1 = 7*(30*(k+1)) := by
              calc
                _ = 210 * (k + 1) := by apply claim2
                _ = _ := by ring
            rw [this]
            exact Nat.dvd_mul_right 7 (30 * (k + 1))
            simp
  done