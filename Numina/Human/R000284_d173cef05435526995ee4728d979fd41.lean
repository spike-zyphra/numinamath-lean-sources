import Mathlib
import Aesop
open BigOperators Real Nat Topology Rat

/-
  Find all the values that can take the last digit of a "perfect" even number.
  (The natural number  $n$  is called "perfect" if the sum of all its natural divisors
  is equal twice the number itself.For example: the number  $6$  is perfect ,because  $1+2+3+6=2\cdot6$ ).
-/
theorem number_theory_8812 :
    {d : ℕ | ∃ n : ℕ, Even n ∧ Nat.Perfect n ∧ d = n % 10} = {6, 8} := by

  apply Set.ext
  intro x
  constructor
  · -- intro d, prove d % 10 = 6 or 8
    rintro ⟨d, ⟨heven, ⟨hperfect, hmod⟩⟩⟩
    -- prove d > 0
    have d_pos : d > 0 := by apply hperfect.right
    let k := d.factorization 2
    -- let d = 2 ^ k * p for some p
    obtain ⟨p, hmul⟩ : 2 ^ k ∣ d := by exact ord_proj_dvd d 2
    have hmul' := hmul
    have hk : k ≥ 1 := by
      by_contra hlt
      simp at hlt
      have : ¬ 2 ∣ d := by
        rw [<-Nat.pow_one 2, <-Nat.zero_add 1, <-hlt]
        refine pow_succ_factorization_not_dvd ?_ ?_
        · exact not_eq_zero_of_lt d_pos
        · trivial
      have : 2 ∣ d := by exact even_iff_two_dvd.mp heven
      contradiction
    -- prove 2^k and p are coprime
    have hcop : Coprime (2 ^ k) p := by
      refine Coprime.pow_left k ?_
      by_contra hdvd
      simp [Even] at hdvd
      obtain ⟨r, hr⟩ := hdvd
      rw [hr] at hmul
      have : 2 ^ (k + 1) ∣ d := by
        rw [hmul]
        ring_nf
        rw [Nat.mul_assoc, <-Nat.pow_add_one]
        exact Nat.dvd_mul_left (2 ^ (k + 1)) r
      have : ¬ 2 ^ (k + 1) ∣ d := by
        refine pow_succ_factorization_not_dvd ?_ ?_
        · exact not_eq_zero_of_lt d_pos
        · trivial
      contradiction
    -- σ(d)=2d by definition
    have hsum : ∑ i ∈ divisors d, i = 2 * d := by
      exact (perfect_iff_sum_divisors_eq_two_mul d_pos).mp hperfect
    -- σ(d)=σ(2^k)σ(p)
    have hsum_mul : ∑ i ∈ divisors d, i = (∑ i ∈ divisors (2 ^ k), i) * ∑ i ∈ divisors p, i := by
      rw [hmul]
      exact Nat.Coprime.sum_divisors_mul hcop
    have hsum : (∑ i ∈ divisors (2 ^ k), i) * ∑ i ∈ divisors p, i = 2 ^ (k + 1) * p := by
      rw [<-hsum_mul, hsum, hmul]
      ring
    have hsum_2 : (∑ i ∈ divisors (2 ^ k), i) = 2 ^ (k + 1) - (1 : ℤ) := by
      rw [Nat.sum_divisors_prime_pow]
      · induction k with
        | zero => simp
        | succ k ih =>
          push_cast at ih
          rw [Finset.sum_range_succ]
          push_cast
          rw [ih]
          ring_nf
      · trivial
    have : (2 : ℕ) ^ (k + 1) - (1 : ℕ) = 2 ^ (k + 1) - (1 : ℤ) := by
      norm_cast
    have hge : 2 ^ (k + 1) ≥ 1 := by exact Nat.one_le_two_pow
    rw [<-this, <-Nat.cast_pow, <-Nat.cast_sub hge] at hsum_2
    norm_cast at hsum_2
    rw [hsum_2] at hsum
    have hproper : ∑ i ∈ divisors p, i = ∑ i ∈ properDivisors p, i + p:= by
      exact sum_divisors_eq_sum_properDivisors_add_self

    -- obtain p ∣ σ*(p)
    have hmul : (∑ i ∈ properDivisors p, i) * (2 ^ (k + 1) - 1) = p := by
      calc
        (∑ i ∈ properDivisors p, i) * (2 ^ (k + 1) - 1) = (∑ i ∈ divisors p, i - p) * (2 ^ (k + 1) - 1) := by rw [hproper]; simp
        _ = (∑ i ∈ divisors p, i) * (2 ^ (k + 1) - 1) - p * (2 ^ (k + 1) - 1) := by simp [Nat.sub_mul]
        _ = 2 ^ (k + 1) * p - p * (2 ^ (k + 1) - 1) := by simp [<-hsum, mul_comm]
        _ = 2 ^ (k + 1) * p - p * 2 ^ (k + 1) + p := by
          rw [Nat.mul_sub, Nat.mul_one]
          apply (@Nat.cast_inj ℤ _ _).mp
          rw [Nat.cast_sub, Nat.cast_sub, Nat.cast_add, Nat.cast_sub]
          · ring
          · rw [mul_comm]
          · exact Nat.le_mul_of_pos_right p hge
          · simp [mul_comm]
        _ = p := by simp [mul_comm]
    have : (∑ i ∈ properDivisors p, i) ∣ p := by use (2 ^ (k + 1) - 1); rw [hmul]

    -- therefore, σ*(p) = 1 ∨ σ*(p) = p
    have : (∑ i ∈ properDivisors p, i) = 1 ∨ (∑ i ∈ properDivisors p, i) = p := by
      exact sum_properDivisors_dvd this

    rcases this with h | h
    · -- if σ*(p) = 1, then p is a prime and p = 2^(k+1)-1
      have hp : Nat.Prime p := by
        exact sum_properDivisors_eq_one_iff_prime.mp h
      have : p = (2 ^ (k + 1) - 1) := by rw [h] at hmul; rw [<-hmul]; simp
      rw [this] at hmul'
      rw [hmul'] at hmod
      simp [hmod]
      -- d=2 ^ k * (2 ^ (k + 1) - 1)
      rw [this] at hp
      -- d % 10 = 6 or 8 <- d % 5 =3 or 4
      let a := k / 4
      let b := k % 4
      have hdecom : k = a * 4 + b := by exact Eq.symm (div_add_mod' k 4)
      have : b < 4 := by apply Nat.mod_lt; trivial
      have : Fact (Nat.Prime 5) := by exact {out := (show Nat.Prime 5 by decide)}
      have hfer : 2 ^ 4 = (1 : ZMod 5) := by exact rfl
      have : 2 ^ k = (2 ^ b : ZMod 5) := by
        calc
          (2 ^ k : ZMod 5) = (2 ^ 4) ^ a * 2 ^ b := by rw [hdecom, pow_add]; nth_rw 2 [mul_comm]; rw [pow_mul]
          _ = 2 ^ b := by simp [hfer]
      have h : 2 ^ (k - 1) = (3 * 2 ^ b : ZMod 5) := by
        rw [<-mul_one (2 ^ (k - 1)), <-hfer, <-pow_add, show (4 = 1 + 3) by simp, <-Nat.add_assoc, Nat.sub_add_cancel]
        rw [pow_add, mul_comm, <-this]
        norm_num
        · apply Or.inl
          exact rfl
        · exact hk
      -- obtain 2 ^ (k - 1) * (2 ^ (k + 1) - 1) ≡ 3 * 2 ^ b * (2 * 2 ^ b - 1) [ZMOD 5]
      have : 2 ^ (k - 1) * (2 ^ (k + 1) - 1) = (3 * 2 ^ b * (2 * 2 ^ b - 1) : ZMod 5) := by
        rw [h, pow_add, pow_one, this]
        nth_rw 3 [mul_comm]
      -- since b < 4, by cases
      interval_cases b
      · -- b = 0 => d % 5 = 3
        have : 2 ^ (k - 1) * (2 ^ (k + 1) - 1) ≡ 3 [MOD 5] := by
          apply (ZMod.eq_iff_modEq_nat 5).mp
          push_cast
          rw [Nat.cast_sub]
          · push_cast
            simp [this]
            norm_num
          · norm_cast
        have : (2 ^ (k - 1) * (2 ^ (k + 1) - 1)) % 5 = 3 % 5 := by exact this
        obtain h := mod_add_div' (2 ^ (k - 1) * (2 ^ (k + 1) - 1)) 5
        rw [this] at h
        -- d % 10 = 6
        have : 6 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * 10 = 2 ^ k * (2 ^ (k + 1) - 1) := by
          calc
            6 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * 10 = 3 * 2 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * (5 * 2) := by norm_num
            _ = (3 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * 5) * 2 := by rw [add_mul, mul_assoc]
            _ = 2 * 2 ^ (k - 1) * (2 ^ (k + 1) - 1) := by rw [h, mul_comm, mul_assoc]
            _ = 2 ^ k * (2 ^ (k + 1) - 1) := by rw [<-Nat.pow_add_one', Nat.sub_add_cancel hk]
        apply Or.inl
        rw [<-this]
        simp
      · -- b = 1 => d % 5 = 3
        have : 2 ^ (k - 1) * (2 ^ (k + 1) - 1) ≡ 3 [MOD 5] := by
          apply (ZMod.eq_iff_modEq_nat 5).mp
          push_cast
          rw [Nat.cast_sub]
          · push_cast
            simp [this]
            norm_num
            exact rfl
          · norm_cast
        have : (2 ^ (k - 1) * (2 ^ (k + 1) - 1)) % 5 = 3 % 5 := by exact this
        obtain h := mod_add_div' (2 ^ (k - 1) * (2 ^ (k + 1) - 1)) 5
        rw [this] at h
        -- d % 10 = 6
        have : 6 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * 10 = 2 ^ k * (2 ^ (k + 1) - 1) := by
          calc
            6 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * 10 = 3 * 2 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * (5 * 2) := by norm_num
            _ = (3 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * 5) * 2 := by rw [add_mul, mul_assoc]
            _ = 2 * 2 ^ (k - 1) * (2 ^ (k + 1) - 1) := by rw [h, mul_comm, mul_assoc]
            _ = 2 ^ k * (2 ^ (k + 1) - 1) := by rw [<-Nat.pow_add_one', Nat.sub_add_cancel hk]
        apply Or.inl
        rw [<-this]
        simp
      · -- b = 2 → d % 5 = 4
        have : 2 ^ (k - 1) * (2 ^ (k + 1) - 1) ≡ 4 [MOD 5] := by
          apply (ZMod.eq_iff_modEq_nat 5).mp
          push_cast
          rw [Nat.cast_sub]
          · push_cast
            simp [this]
            norm_num
            exact rfl
          · norm_cast
        have : (2 ^ (k - 1) * (2 ^ (k + 1) - 1)) % 5 = 4 % 5 := by exact this
        obtain h := mod_add_div' (2 ^ (k - 1) * (2 ^ (k + 1) - 1)) 5
        rw [this] at h
        -- d % 10 = 8
        have : 8 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * 10 = 2 ^ k * (2 ^ (k + 1) - 1) := by
          calc
            8 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * 10 = 4 * 2 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * (5 * 2) := by norm_num
            _ = (4 + 2 ^ (k - 1) * (2 ^ (k + 1) - 1) / 5 * 5) * 2 := by rw [add_mul, mul_assoc]
            _ = 2 * 2 ^ (k - 1) * (2 ^ (k + 1) - 1) := by rw [h, mul_comm, mul_assoc]
            _ = 2 ^ k * (2 ^ (k + 1) - 1) := by rw [<-Nat.pow_add_one', Nat.sub_add_cancel hk]
        apply Or.inr
        rw [<-this]
        simp
      · -- b = 3 → 5 ∣ d = 2^ (k +1)p
        have : 2 ^ (k - 1) * (2 ^ (k + 1) - 1) ≡ 0 [MOD 5] := by
          apply (ZMod.eq_iff_modEq_nat 5).mp
          push_cast
          rw [Nat.cast_sub]
          · push_cast
            rw [this]
            norm_num
            exact rfl
          · norm_cast
        have : 5 ∣ 2 ^ (k - 1) * (2 ^ (k + 1) - 1) := by exact dvd_of_mod_eq_zero this
        have : 5 ∣ 2 ^ (k - 1) ∨ 5 ∣ 2 ^ (k + 1) - 1 := by
          refine (Nat.Prime.dvd_mul ?pp).mp this
          trivial
        rcases this with h | h
        · -- if 5 ∣ 2 ^ (k + 1), then 5 ∣ 2. contradiction
          have : 5 ∣ 2 := by
            apply Nat.Prime.dvd_of_dvd_pow ?_ h
            trivial
          have : ¬ 5 ∣ 2 := by norm_num
          contradiction
        · -- if 5 ∣ p, then p = 5 since p is prime → 2 ^ (k + 1) - 1 = 5
          have : 5 = 2 ^ (k + 1) - 1 := by
            apply (Nat.prime_dvd_prime_iff_eq ?_ hp).mp h
            trivial
          have : 6 = 2 ^ (k + 1) := by
            calc
              6 = 5 + 1 := by simp
              _ = 2 ^ (k + 1) - 1 + 1 := by rw [this]
              _ = 2 ^ (k + 1) := by rw [Nat.sub_add_cancel]; exact hge
          -- 3 ∣ 2 ^ (k + 1) → 3 ∣ 2, contradiction
          have : 3 ∣ 2 ^ (k + 1) := by rw [<-this]; decide
          have : 3 ∣ 2 := by apply Nat.Prime.dvd_of_dvd_pow; trivial; exact this
          norm_num at this
    · -- if σ*(p) = p, then (2 ^ (k + 1) - 1) = 1
      rw [h] at hmul
      have : (2 ^ (k + 1) - 1) = 1 := by
        nth_rw 2 [<-Nat.mul_one p] at hmul
        rw [Nat.mul_right_inj] at hmul
        · exact hmul
        · by_contra heq
          rw [heq] at hcop
          simp at hcop
          have h0 : k = 0 := by
            by_contra hge
            have : 2 ^ k ≥ 2 := by exact Nat.le_self_pow hge 2
            simp [hcop] at this
          linarith
      -- k ≥ 1 → 2 ^ (k + 1) - 1 ≥ 3, contradiction
      have : 2 ^ (k + 1) - 1 ≥ 3 := by
        have : 2 ^ (k + 1) ≥ 2 ^ (1 + 1) := by
          apply Nat.pow_le_pow_of_le
          · trivial
          · rel [hk]
        calc
          2 ^ (k + 1) - 1 ≥ 2 ^ (1 + 1) - 1 := by exact Nat.sub_le_sub_right this 1
          _ = 3 := by simp
      linarith


  · intro hx
    simp at hx
    cases hx with
    | inl hx =>
      -- digit 6, use 6 = 1 + 2 + 3
      use 6
      simp [hx]
      split_ands
      · trivial
      · have : properDivisors 6 = {1, 2, 3} := by
          apply Finset.ext
          intro a
          simp
          constructor
          · intro ha
            obtain ⟨h1, h2⟩ := ha
            revert h1
            interval_cases a
            all_goals decide
          · intro ha
            repeat' rcases ha with ha | ha
            all_goals decide
        rw [this]
        simp
      · trivial
    | inr hx =>
      -- digit 8, use 28 = 1 + 2 + 4 + 7 + 14
      use 28
      simp [hx]
      split_ands
      · trivial
      · have : properDivisors 28 = {1, 2, 4, 7, 14} := by
          apply Finset.ext
          intro a
          simp
          constructor
          · intro ha
            obtain ⟨h1, h2⟩ := ha
            revert h1
            interval_cases a
            all_goals decide
          · intro ha
            repeat' rcases ha with ha | ha
            all_goals decide
        rw [this]
        simp
      · trivial
