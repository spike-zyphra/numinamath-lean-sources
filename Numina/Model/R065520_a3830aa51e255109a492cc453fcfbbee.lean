import Mathlib

theorem algebra_244460 :
    Set.ncard {n : ℕ | n > 0 ∧ Nat.Prime (n ^ 2 + 2 * n)} = 1 := by
  have h1 : {n : ℕ | n > 0 ∧ Nat.Prime (n ^ 2 + 2 * n)} = {1} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume n > 0 and Nat.Prime (n ^ 2 + 2 * n)
      intro h
      rcases h with ⟨h1, h2⟩
      by_cases h3 : n = 1
      · -- n = 1, which is our goal
        exact h3
      · -- n ≠ 1
        have h4 : n ≥ 2 := by
          omega
        have h5 : ¬ Nat.Prime (n ^ 2 + 2 * n) := by
          -- The number is composite since it factors into n * (n + 2)
          apply Nat.not_prime_of_dvd_of_lt (show n ∣ n ^ 2 + 2 * n by
            use n + 2
            ring
          ) (by nlinarith) (by nlinarith)
        contradiction
    · -- Assume n = 1
      intro h
      rw [h]
      constructor
      · norm_num
      · norm_num
  rw [h1]
  simp