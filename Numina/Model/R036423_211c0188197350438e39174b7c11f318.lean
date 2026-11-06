import Mathlib

open Finset Real

theorem algebra_96335 {f : ℝ → ℝ} (hf : ∀ x, f x = 4 * x - x ^ 2) :
    {x | ∃ n, x = f^[n] x}.Infinite := by

  have h8 : Set.Infinite {x | ∃ n, x = f^[n] x} := by
    apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => ((↑n : ℝ)))
    · -- Show (λ (n : ℕ) => (↑n : ℝ)) is injective 
      intro n m h 
      simp at h 
      all_goals 
        omega 
    · -- Show all values are in the set 
      intro n 
      use 0 
      simp [Function.iterate_zero_apply]

  simpa using h8