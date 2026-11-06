import Mathlib

theorem number_theory_1810 : Set.Infinite {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a ^ 4 + b ^ 4 = c ^ 4 + d ^ 4} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => ( ( (n : ℤ) + 1 ) , (n : ℤ) + 1 , (n : ℤ) + 1 , (n : ℤ) + 1 ) )
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that all f(n) are in the set
    intro n
    simp [Prod.ext_iff]
    all_goals
      ring_nf
      <;> norm_num
      <;> try tauto