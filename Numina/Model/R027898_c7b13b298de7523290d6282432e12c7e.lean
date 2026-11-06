import Mathlib

theorem number_theory_197681 (a : Fin 28 → ℕ) (ha : ∀ i, a i = 1) :
    IsGreatest {∑ i, ∑ j, if i < j then a i * a j else 0} 378 := by
  have h1 : (∑ i : Fin 28, ∑ j : Fin 28, if i < j then a i * a j else 0) = 378 := by
    simp [ha]
    <;> native_decide
  constructor
  · -- Show 378 is in the set.
    rw [h1]
    all_goals
      simp
  · -- Show no greater value is in the set.
    intro s hs
    have h2 : s = (∑ i : Fin 28, ∑ j : Fin 28, if i < j then a i * a j else 0) := by
      simpa using hs
    rw [h2, h1]
    all_goals
      all_goals
        omega