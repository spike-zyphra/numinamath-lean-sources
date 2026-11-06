import Mathlib

theorem number_theory_197604 (a : Fin 29 → ℕ) (ha : ∀ i, a i = 1) :
    IsGreatest {∑ i, ∑ j, if i < j then a i * a j else 0} 406 := by 
  simp_all [IsGreatest, Set.mem_singleton_iff]
  <;> native_decide