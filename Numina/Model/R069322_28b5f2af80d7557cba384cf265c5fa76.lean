import Mathlib

theorem number_theory_16386 :
    (Nat.card {p | p.Prime ∧ p ∈ Finset.Icc 1 50 ∧ 7 ∣ p}) / 50 = 1 / 50 := by
  have h1 : {p | p.Prime ∧ p ∈ Finset.Icc 1 50 ∧ 7 ∣ p} = {7} := by
    ext p
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Suppose p is a prime, p ∈ [1, 50], and 7 ∣ p
      intro hp
      rcases hp with ⟨h_prime, ⟨hp1, hp2⟩, hdiv⟩
      interval_cases p <;> norm_num at h_prime hdiv <;> omega
    · -- If p = 7, then it satisfies the conditions
      intro hp
      rw [hp]
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
  rw [h1]
  norm_num