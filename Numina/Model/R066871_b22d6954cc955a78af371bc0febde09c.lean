import Mathlib

theorem number_theory_121918 :
    Set.Infinite {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a^3 + b^4 + c^5 = d^7} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (0, 0, n^7, n^5))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h 
    all_goals 
      omega
  · -- Show that all elements in the image of f satisfy the equation
    intro n
    simp [Prod.ext_iff]
    all_goals 
      ring_nf