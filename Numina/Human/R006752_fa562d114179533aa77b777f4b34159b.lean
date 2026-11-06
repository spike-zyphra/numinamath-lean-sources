import Mathlib

open Nat Finset

def is_abundant (n : ℕ) := ∑ d in n.properDivisors, d > n

lemma sum_range_two_pow (k : ℕ) : (∑ x ∈ Finset.range (k + 1), (2 : ℤ) ^ x) = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => 
    simp
  | succ n ih => 
    rw [range_add_one, sum_insert]
    nth_rw 2 [pow_add]
    simp
    rw [ih]
    omega
    simp

theorem number_theory_640801 (k : ℕ) (hk : 0 < k) :
  is_abundant (7 * 2 ^ k) ↔ k ≥ 3 := by 
  -- first simplify the sum of all properDivisors, using the formula, `∑ d ∈ n.divisors, d = ∏ p ∈ n.primeFactors, ∑ k ∈ range (n.factorization p + 1), p ^ k` and the formula `∑ i ∈ n.divisors, i = ∑ i ∈ n.properDivisors, i + n`
  have h1 : ∑ d ∈ (7 * 2 ^ k : ℕ).properDivisors, (d : ℤ) = (∑ x ∈ range (k + 1), 2 ^ x) * 8 - 7 * 2 ^ k := by 
    obtain h1 := @sum_divisors_eq_sum_properDivisors_add_self (7 * 2 ^ k)
    zify at h1
    have aux1 : ∑ x ∈ (7 * 2 ^ k : ℕ).properDivisors, (x : ℤ) = 
      ∑ x ∈ (7 * 2 ^ k : ℕ).divisors, ↑x - 7 * 2 ^ k := by 
      linarith
    obtain h2 := @sum_divisors (7 * 2 ^ k) (by positivity)
    zify at h2
    rw [h2] at aux1
    have aux2 : (7 * 2 ^ k).primeFactors = {2, 7} := by 
      refine Finset.ext_iff.mpr ?_
      intro p 
      constructor
      · intro hp
        simp at hp
        obtain ⟨hp1, hp2⟩ := hp
        have pdvd_or : p ∣ 7 ∨ p ∣ 2 ^ k := by 
          exact (Nat.Prime.dvd_mul hp1).mp hp2
        obtain pdvd | pdbd := pdvd_or
        · have peq7 : p = 7 := by
            refine (Nat.prime_dvd_prime_iff_eq hp1 (by norm_num)).mp pdvd
          rw [peq7]
          simp
        · have peq2 : p = 2 := by 
            have pdvd2 : p ∣ 2 := by 
              exact Nat.Prime.dvd_of_dvd_pow hp1 pdbd
            refine (Nat.prime_dvd_prime_iff_eq hp1 (by norm_num)).mp pdvd2
          rw [peq2]
          simp
      · intro hp
        simp at hp
        obtain hp1 | hp2:= hp
        · rw [hp1]
          simp
          norm_num
          have dvd1 : 2 ∣ 2 ^ k := by 
            refine dvd_pow_self 2 ?_
            linarith
          exact (Coprime.dvd_mul_left rfl).mpr dvd1
        · simp [hp2]
          norm_num
    simp [aux2] at aux1
    norm_num at aux1
    exact aux1
  constructor
  · intro h
    -- Nat.sum_divisors
    unfold is_abundant at h
    zify at h
    rw [h1] at h
    rw [sum_range_two_pow k, pow_add] at h
    ring_nf at h
    have lt1 : 8 < (2 : ℤ) * 2 ^ k := by 
      linarith
    by_contra hc
    simp at hc
    have klt : k ≤ 2 := by 
      linarith
    have lt2 : 2 ^ k ≤  2 ^ 2 := by 
      apply pow_le_pow_right₀ 
      linarith
      exact klt
    linarith
  · intro h
    unfold is_abundant
    zify
    rw [h1]
    rw [sum_range_two_pow k, pow_add]
    ring_nf
    have kge : 2 ^ k ≥ 2 ^ 3 := by 
      apply pow_le_pow_right₀
      linarith
      exact h
    linarith
