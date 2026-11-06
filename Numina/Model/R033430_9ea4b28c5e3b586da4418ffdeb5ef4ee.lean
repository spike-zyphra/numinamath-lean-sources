import Mathlib

theorem number_theory_221388 : Set.Infinite {(x, y, z) : ℕ × ℕ × ℕ | x^2 + y^3 = z^5} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (2 ^ (15 * n + 12), 2 ^ (10 * n + 8), 2 ^ (6 * n + 5)))
  · -- Show f is injective.
    intro n m h 
    simp [Prod.ext_iff] at h 
    all_goals 
      omega
  · -- Show that all elements in the image of f are in the set.
    intro n 
    simp [Prod.ext_iff]
    all_goals
      have eq1 : (2 ^ (15 * n + 12) : ℕ) ^ 2 + (2 ^ (10 * n + 8) : ℕ) ^ 3 = (2 ^ (6 * n + 5) : ℕ) ^ 5 := by
        have h1 : (2 ^ (15 * n + 12) : ℕ) ^ 2 = 2 ^ (30 * n + 24) := by
          ring_nf
        have h2 : (2 ^ (10 * n + 8) : ℕ) ^ 3 = 2 ^ (30 * n + 24) := by
          ring_nf
        have h3 : (2 ^ (6 * n + 5) : ℕ) ^ 5 = 2 ^ (30 * n + 25) := by
          ring_nf
        rw [h1, h2, h3]
        ring_nf
      tauto