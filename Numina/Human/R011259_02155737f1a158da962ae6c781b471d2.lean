import Mathlib

open Nat

theorem number_theory_233621 (p : Finset ℕ) (hp : ∀ n ∈ p, Nat.Prime n)
    (h : ∏ n ∈ p, n = 30030) :
    Nat.Prime (∑ n ∈ p, n) := by 

    --We prove that these primes have to be 2,3,5,7,11,13, which form a prime decomposition of 30030.
    have lem : p = {2,3,5,7,11,13} := by 
      have pd30030 : Nat.primeFactors 30030 = {2,3,5,7,11,13} := by native_decide
      rw [← pd30030]
      
      ext x
      simp
      
      constructor
      
      intro xinp
      constructor
      apply hp at xinp
      exact xinp
      
      rw [← h]
      exact Finset.dvd_prod_of_mem (fun i => i) xinp

      intro ⟨xp, xd⟩
      rw [← h] at xd
      have : ∃ y ∈ p, x ∣ y := by 
        rw [Prime.dvd_finset_prod_iff] at xd
        exact xd
        exact prime_iff.mp xp
      obtain ⟨y,yinp, xdy⟩ := this
      rw [prime_dvd_prime_iff_eq] at xdy
      rw [xdy]
      exact yinp
      exact xp
      apply hp at yinp
      exact yinp
    
    --Now just sum them up.
    simp [lem]
    norm_num
