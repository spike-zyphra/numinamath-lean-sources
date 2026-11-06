import Mathlib

theorem number_theory_6455 : {(x : ZMod 5) | 3*x^14+4*x^13+2*x^11+x^9+x^6+x^3+12*x^2+x=0} =
    {0,1,2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  have h1 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
    fin_cases x <;> simp
  rcases h1 with (r | r | r | r | r)
  · -- x = 0
    rw [r]
    native_decide
  · -- x = 1
    rw [r]
    native_decide
  · -- x = 2
    rw [r]
    native_decide
  · -- x = 3
    rw [r]
    native_decide
  · -- x = 4
    rw [r]
    native_decide