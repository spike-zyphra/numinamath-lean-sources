import Mathlib

theorem number_theory_118258 : Set.Infinite {(a, b) : ℤ × ℤ | a * (a + 1) ∣ b ^ 2 + 1} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (1, (2 : ℤ) * (n : ℤ) + 1))
  · -- Show that the function is injective
    intro n m h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that all elements of the image are in the set
    intro n
    simp [Prod.ext_iff]
    all_goals
      ring_nf
      all_goals
        norm_num
        all_goals
          ring_nf
          <;> omega