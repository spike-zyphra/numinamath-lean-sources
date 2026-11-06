import Mathlib

theorem number_theory_70947 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x ^ 2 + y ∣ x + y ^ 2}.Infinite := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => ((n + 1 : ℕ), (n + 1 : ℕ)))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    omega 
  · -- Show that all elements in the image of f are in the set
    intro n 
    simp [Prod.ext_iff, show (n + 1 : ℕ) > 0 by omega]
    all_goals 
      ring_nf
      <;> norm_num
      all_goals 
        ring_nf