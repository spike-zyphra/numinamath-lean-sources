import Mathlib

def f (A B : Set ℤ) : Set ℤ := {x | x ∈ A ∧ ¬(x ∈ B)} ∪ {x | x ∈ B ∧ ¬(x ∈ A)}

theorem other_196603 {X Y : Set ℤ} (hX : X = {1, 3, 5, 7}) (hY : Y = {x | abs x < 4}) :
    f X Y = {-1, -2, -3, 0, 2, 5, 7} := by 
  rw [f]
  rw [hX, hY]
  ext x
  simp [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Suppose x ∈ f X Y, we'll show x ∈ {-1, -2, -3, 0, 2, 5, 7}
    intro h
    rcases h with (h | h)
    · -- Case where x ∈ X ∧ ¬(x ∈ Y)
      rcases h with ⟨hx1, hx2⟩
      rcases hx1 with (rfl | rfl | rfl | rfl)
      · -- x = 1: Contradiction since |1| < 4
        exfalso
        norm_num [abs_lt] at hx2
      · -- x = 3: Contradiction since |3| < 4
        exfalso
        norm_num [abs_lt] at hx2
      · -- x = 5: Valid
        norm_num [abs_lt] at *
      · -- x = 7: Valid
        norm_num [abs_lt] at *
    · -- Case where x ∈ Y ∧ ¬(x ∈ X)
      rcases h with ⟨hx1, hx2⟩
      have h2 : x ≤ 3 := by 
        by_cases h2 : x ≥ 0 
        · -- x ≥ 0, |x| < 4 implies x < 4
          rw [abs_of_nonneg h2] at hx1
          linarith 
        · -- x < 0, |x| < 4 implies -x < 4 
          push_neg at h2 
          rw [abs_of_neg h2] at hx1 
          linarith
      have h3 : x ≥ -3 := by 
        by_cases h4 : x ≥ 0 
        · -- x ≥ 0, |x| < 4 implies x < 4 
          rw [abs_of_nonneg h4] at hx1 
          omega 
        · -- x < 0, |x| < 4 implies -x < 4 
          push_neg at h4 
          rw [abs_of_neg h4] at hx1 
          omega 
      interval_cases x <;> tauto
  · -- Now the reverse direction: if x ∈ {-1, -2, -3, 0, 2, 5, 7}, then x ∈ f X Y
    intro h
    rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- x = -1: Show that x ∈ Y ∧ ¬(x ∈ X)
      simp [abs]
    · -- x = -2: Show that x ∈ Y ∧ ¬(x ∈ X)
      simp [abs]
    · -- x = -3: Show that x ∈ Y ∧ ¬(x ∈ X)
      simp [abs]
    · -- x = 0: Show that x ∈ Y ∧ ¬(x ∈ X)
      simp [abs]
    · -- x = 2: Show that x ∈ Y ∧ ¬(x ∈ X)
      simp [abs]
    · -- x = 5: Show that x ∈ X ∧ ¬(x ∈ Y)
      simp [abs]
    · -- x = 7: Show that x ∈ X ∧ ¬(x ∈ Y)
      simp [abs]