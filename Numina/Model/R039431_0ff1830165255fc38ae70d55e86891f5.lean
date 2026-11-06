import Mathlib
open Nat Real Finset Set

theorem number_theory_600021 :
    {n | n ≥ 1 ∧ fib n = n ^ 2} = {1, 12} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume h: n >= 1 ∧ fib n = n ^ 2, prove n in {1, 12}
    intro h
    rcases h with ⟨h1, heq⟩
    have h2 : n ≤ 12 := by
      by_contra h
      push_neg at h
      have h4 : n >= 13 := by omega
      have h5 : fib n > n ^ 2 := by
        have h6 : ∀ k, fib (k + 13) > (k + 13) ^ 2 := by
          intro k
          induction' k using Nat.strongRecOn with k ih
          cases k with
          | zero =>
            norm_num [fib]
          | succ k =>
            have h6k := ih k (by linarith)
            have h6k1 := ih (k) (by linarith)
            simp [fib_add_one, pow_two] at h6k h6k1 ⊢
            nlinarith [h6k, h6k1, sq_nonneg (fib (k + 13) - (k + 13) ^ 2), sq_nonneg (k + 13), sq_nonneg (k + 13 - 1)]
        specialize h6 (n - 13)
        have h7 : (n - 13) + 13 = n := by omega
        rw [h7] at h6
        exact h6
      nlinarith [heq, h5]
    interval_cases n <;> norm_num [fib] at heq ⊢ <;> tauto
  · -- Assume n in {1, 12}, prove h: n >= 1 ∧ fib n = n ^ 2
    rintro (rfl | rfl)
    · -- n = 1
      constructor <;> norm_num [fib]
    · -- n = 12
      constructor <;> norm_num [fib]