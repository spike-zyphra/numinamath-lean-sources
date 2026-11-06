import Mathlib

open Finset Nat

theorem number_theory_635332 (k N Sk: ℕ) (hk : 0 < k) (hN : N = (6 * k) ^ 2)
  (A : ℕ) (hA : A = ∏ x ∈ (Nat.divisors N), x) (hS : Sk = ∑ x ∈ (Nat.primeFactors (6 * k)), x) :
  ∑ x ∈ (Nat.primeFactors A), x = Sk := by 
  rw [hS]
  have seteq : A.primeFactors =  Nat.primeFactors (6 * k) := by
    refine Finset.ext_iff.mpr ?_
    intro x
    constructor
    · simp
      intro hx xdvd neq
      constructor
      exact hx
      -- Prime.exists_mem_finset_dvd
      rw [hA] at xdvd 
      have aux1 : _root_.Prime x := by 
        exact prime_iff.mp hx
      obtain ⟨i, hi1, hi2⟩ := Prime.exists_mem_finset_dvd aux1 xdvd
      simp at hi1
      obtain ⟨hi1, hi1'⟩ := hi1
      have xdvd2 : x ∣ N := by exact dvd_trans hi2 hi1
      rw [hN] at xdvd2
      have xdvd3 : x ∣ (6 * k) := by 
        exact Nat.Prime.dvd_of_dvd_pow hx xdvd2
      constructor
      exact xdvd3
      positivity
    · simp 
      intro hx xdvd kneq 
      constructor
      · exact hx
      constructor
      · rw [hA]
        have xmem : x ∈ N.divisors := by 
          simp
          constructor
          · rw [hN]
            refine Dvd.dvd.pow xdvd ?_
            norm_num
          · nlinarith
        exact dvd_prod_of_mem (fun i => i) xmem
      rw [hA]
      refine Nat.ne_zero_iff_zero_lt.mpr ?_
      apply Finset.prod_pos
      intro i hi
      simp at hi
      obtain ⟨hi1, hi2⟩ := hi
      obtain ⟨m, hm⟩ := hi1
      nlinarith
  rw [seteq]