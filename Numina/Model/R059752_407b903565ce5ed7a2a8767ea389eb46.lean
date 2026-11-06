import Mathlib

def empty_set : Set ℕ := ∅
def set_0 : Set ℕ := {0}

theorem other_312148 : empty_set ⊂ set_0 := by
  unfold empty_set set_0
  constructor
  · -- show that ∅ ⊆ {0}
    simp
  · -- show that ∅ ≠ {0}
    simp