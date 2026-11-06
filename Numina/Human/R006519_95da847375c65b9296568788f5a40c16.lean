import Mathlib

theorem number_theory_638002 (k : ℕ) (hk : 0 < k) :
    (10 ^ k).divisors.card = (k + 1) ^ 2 := by
  rw [Nat.card_divisors]
  have h1 : (10 ^ k).primeFactors = {2, 5} := by 
    refine Finset.ext_iff.mpr ?_
    intro a 
    constructor
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    have advd : a ∣ 10 := by 
      exact Nat.Prime.dvd_of_dvd_pow h1 h2
    rw [show 10 = 2 * 5 by norm_num] at advd
    have advd_or : a∣ 2 ∨ a∣ 5 := by 
      exact (Nat.Prime.dvd_mul h1).mp advd
    obtain h3 | h3 := advd_or
    have aeq2 : a = 2 := by
      have prime2 : Nat.Prime 2 := by norm_num
      exact (Nat.prime_dvd_prime_iff_eq h1 prime2).mp h3
    simp [aeq2]
    have aeq5 : a = 5 := by
      have prime5 : Nat.Prime 5 := by norm_num
      exact (Nat.prime_dvd_prime_iff_eq h1 prime5).mp h3
    simp [aeq5]
    · intro h
      simp at h
      obtain h | h := h
      rw [h]
      simp
      constructor
      · norm_num
      · have dvd1 : 2 ∣ 10 := by norm_num
        refine dvd_trans dvd1 ?_
        refine Dvd.dvd.pow ?_ ?_
        simp
        linarith
      simp
      rw [h]
      constructor
      · norm_num
      · have dvd1 : 5 ∣ 10 := by norm_num
        refine dvd_trans dvd1 ?_
        refine Dvd.dvd.pow ?_ ?_
        simp
        linarith
  rw [h1]
  simp
  have eq1 : (Nat.factorization 10) 2 = 1 := by 
    rw [←Nat.multiplicity_eq_factorization]
    refine multiplicity_eq_of_dvd_of_not_dvd ?_ ?_
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  have eq2 : (Nat.factorization 10) 5 = 1 := by 
    rw [←Nat.multiplicity_eq_factorization]
    refine multiplicity_eq_of_dvd_of_not_dvd ?_ ?_
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  rw [eq1, eq2]
  ring
  positivity