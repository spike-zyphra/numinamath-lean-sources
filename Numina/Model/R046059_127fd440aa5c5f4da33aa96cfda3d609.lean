import Mathlib

theorem number_theory_195267 (a : Fin 30 → ℕ) (ha : ∀ i, a i = 1) :
    IsGreatest {∑ i, ∑ j, if i < j then a i * a j else 0} 435 := by
  have h1 : (∑ i : Fin 30, ∑ j : Fin 30, if i < j then a i * a j else 0) = 435 := by
    simp [ha]
    <;> native_decide
  constructor
  · -- Show that 435 is in the set
    simp [h1]
  · -- Show that 435 is greatest in the set
    intro x hx
    simp [h1] at hx
    all_goals linarith