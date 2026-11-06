import Mathlib

theorem algebra_164294 {A B C : Set X} :
    A ∪ (B ∪ C) = (A ∪ B) ∪ C ∧ A ∩ (B ∩ C) = (A ∩ B) ∩ C := by 
  constructor
  · -- Prove associativity of union
    ext x
    simp 
    <;> tauto
  · -- Prove associativity of intersection
    ext x
    simp 
    <;> tauto