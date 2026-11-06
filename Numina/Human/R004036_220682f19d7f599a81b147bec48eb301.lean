import Mathlib
/- 1. Determine all prime numbers of the form $1+2^{p}+3^{p}+\ldots+p^{p}$ where $p$ is a prime number. -/
theorem number_theory_232232 : {q : ℕ | Nat.Prime q ∧ (∃ p : ℕ, Nat.Prime p ∧ q = ∑ i in Finset.range p, (i + 1) ^ p)} = {5}:= by
  ext q
  constructor
  .
    -- Forward direction: if q is in the set, then q = 5
    intro ⟨h1, h2⟩
    rcases h2 with ⟨p, h3, h4⟩
    -- p is prime and q = sum of (i+1)^p for i from 0 to p-1
    have hp : p ≠ 0 := Nat.Prime.ne_zero h3
    simp
    -- Fermat's Little Theorem: for any t coprime to p, t^(p-1) ≡ 1 (mod p)
    have h5 (t : ℕ) (ht0 : t < p) (ht1: 0 < (t : ℕ)) : t ^ (p - 1) ≡ 1 [MOD p] := by
      rw [←show p.totient = p - 1 by exact Nat.totient_prime h3]
      have h6: (t : ℕ).Coprime p := by
        refine Nat.coprime_comm.mp ?_
        exact Nat.coprime_of_lt_prime ht1 ht0 h3
      exact Nat.ModEq.pow_totient h6
    -- For any i, (i+1)^p ≡ (i+1) (mod p)
    have h6 : ∀ i : ℕ, (i + 1) ^ p ≡ i + 1 [MOD p] := by
      intro i
      by_cases hi : p ∣ i + 1
      .
        -- Case 1: p divides i+1, so (i+1)^p ≡ 0^p ≡ 0 ≡ (i+1) (mod p)
        replace hi : i + 1 ≡ 0 [MOD p] := by exact Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat hi)
        have h : (i + 1) ^ p ≡ 0 ^ p [MOD p] := by exact Nat.ModEq.pow p hi
        rw [show 0 ^ p = 0 by exact zero_pow_eq_zero.mpr hp] at h
        exact Nat.ModEq.trans h (id (Nat.ModEq.symm hi))
      .
        -- Case 2: p doesn't divide i+1, use Fermat's Little Theorem
        replace h1 : Nat.Coprime p (i + 1) := by
          exact (Nat.Prime.coprime_iff_not_dvd h3).mpr hi
        have h6 : (i + 1) ^ (p - 1) ≡ 1 [MOD p] := by
          rw [←show p.totient = p - 1 by exact Nat.totient_prime h3]
          refine Nat.ModEq.pow_totient (by exact Nat.coprime_comm.mp h1)
        have h10 : (i + 1) * (i + 1) ^ (p - 1) ≡ (i + 1) * 1 [MOD p] := Nat.ModEq.mul rfl h6
        rw [←show (i + 1) ^ (p - 1 + 1) = (i + 1) * (i + 1) ^ (p - 1) by ring] at h10
        rw [show p - 1 + 1 = p by omega] at h10
        simp at h10
        exact h10
    -- The sum ∑(i+1)^p ≡ ∑(i+1) (mod p)
    have h7 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (i + 1) ^ p ≡ ∑ i in Finset.range n, (i + 1) [MOD p] := by
      intro n
      induction n with
      | zero =>
        simp
        rfl
      | succ n hn1 =>
        repeat rw [Finset.sum_range_succ]
        replace h6 := h6 n
        exact Nat.ModEq.add hn1 h6
    replace h7 := h7 p
    rw [←h4] at h7
    -- Multiply both sides by 2
    replace h7 : 2 * q ≡ 2 * ∑ i ∈ Finset.range p, (i + 1) [MOD p] := Nat.ModEq.mul rfl h7
    -- Formula for sum of first n natural numbers: 2 * ∑(i+1) = n * (n+1)
    have h8 : ∀ n : ℕ, 2 * ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n hni =>
        repeat rw [Finset.sum_range_succ]
        linarith
    replace h8 := h8 p
    rw [h8] at h7
    by_cases hp1 : p = 2
    .
      -- Case: p = 2, directly calculate q = 1^2 + 2^2 = 1 + 4 = 5
      subst p
      simp [Finset.sum_range_succ] at h4
      exact h4
    .
      -- Case: p ≠ 2, show that p must divide q
      have hp2 : p ∣ p * (p + 1) := by simp
      replace hp2 : p * (p + 1) ≡ 0 [MOD p] := by exact Nat.modEq_zero_iff_dvd.mpr hp2
      replace h7 : 2 * q ≡ 0 [MOD p] := Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm hp2)) (id (Nat.ModEq.symm h7)))
      replace h7 : p ∣ 2 * q := by exact Nat.dvd_of_mod_eq_zero h7
      -- p is odd (since p ≠ 2), so p is coprime to 2
      have h8 : Nat.Coprime p 2 := by refine Nat.coprime_two_right.mpr (Nat.Prime.odd_of_ne_two h3 hp1)
      replace h7 : p ∣ q := by exact Nat.Coprime.dvd_of_dvd_mul_left h8 h7
      -- Since p is prime and divides q, and q is prime, we must have p = q
      replace h7 : p = q := by exact (Nat.prime_dvd_prime_iff_eq h3 h1).mp h7
      by_contra h
      subst q
      -- Show that the sum is too large for p > 5
      have h9 : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 2), (i + 1) ^ p ≥ ∑ i ∈ Finset.range 2, (i + 1) ^ p := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n hni =>
          rw [show n + 1 + 2 = (n + 2) + 1 by omega]
          rw [Finset.sum_range_succ]
          omega
      replace h9 := h9 (p - 2)
      replace hp : p > 1 := by exact Nat.Prime.one_lt h3
      rw [show (p - 2 + 2) = p by omega] at h9
      simp [Finset.sum_range_succ] at h9
      -- Show that 2^p ≥ p + 1 for all p
      have h10 : ∀ n, 2 ^ n ≥ n + 1 := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n hni =>
          ring_nf
          linarith
      replace h10 := h10 p
      linarith

  .
    -- Backward direction: if q = 5, then q is in the set (with p = 2)
    intro h
    simp at h ⊢
    constructor
    .
      -- Show that 5 is prime
      rw [h]
      exact Nat.prime_five
    .
      -- Show that 5 can be expressed as sum with p = 2
      use 2
      constructor
      .
        -- 2 is prime
        exact Nat.prime_two
      .
        -- Calculate: 1^2 + 2^2 = 1 + 4 = 5
        norm_num
        exact h
