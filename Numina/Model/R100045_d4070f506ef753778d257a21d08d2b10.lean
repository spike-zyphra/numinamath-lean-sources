import Mathlib

theorem algebra_264911 {A B C : Set X} : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) ∧
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  constructor
  · -- First part: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)
    ext x
    simp [Set.mem_union, Set.mem_inter]
    <;> tauto
  · -- Second part: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)
    ext x
    simp [Set.mem_union, Set.mem_inter]
    <;> tauto