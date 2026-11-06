import Mathlib

theorem number_theory_8653 :
    {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a^3 + b^4 + c^5 = d^7}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n) => ( (n + 1)^7, 0, 0, (n + 1)^3 ) )
  · -- Show that f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    all_goals omega
  · -- Show that for all n, f(n) is in the set
    intro n
    simp [Prod.ext_iff]
    <;> ring_nf
    all_goals omega