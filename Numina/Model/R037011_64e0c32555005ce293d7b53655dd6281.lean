import Mathlib

theorem number_theory_68006 : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a ^ 3 + b ^ 4 + c ^ 5 = d ^ 7}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (2^(7*t), 0, 0, 2^(3*t)))
  · -- Show f is injective
    intro t s h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that all elements produced by f are in the set
    intro t
    simp [Prod.ext_iff]
    <;> ring_nf
  all_goals omega