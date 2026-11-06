import Mathlib

open Finset Real

theorem inequalities_603670 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i j, i < j → a i ≤ a j) (hb : ∀ i j, i < j → b i ≥ b j) :
    IsGreatest {x | ∃ i, x = a i + b i} ≥ IsGreatest {x | ∃ i, x = a i + b i ∧ i < n} := by
  have h1 : IsGreatest {x | ∃ i, x = a i + b i} = IsGreatest {x | ∃ i, x = a i + b i ∧ i < n} := by
    have h2 : {x | ∃ i, x = a i + b i} = {x | ∃ i, x = a i + b i ∧ i < n} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
      constructor
      · -- Assume x in left side, need to show in right side
        rintro ⟨i, rfl⟩
        refine ⟨i, rfl, Fin.is_lt i⟩
      · -- Assume x in right side, need to show in left side
        rintro ⟨i, rfl, h⟩
        refine ⟨i, rfl⟩
    rw [h2]
  rw [h1]
  all_goals
    simp