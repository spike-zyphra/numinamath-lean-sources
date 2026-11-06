import Mathlib

open Set

theorem algebra_178932 {A B C : Set X} :
    A ∪ B = B ∪ A ∧ A ∩ B = B ∩ A ∧
    A ∪ (B ∪ C) = (A ∪ B) ∪ C ∧ A ∩ (B ∩ C) = (A ∩ B) ∩ C ∧
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ∧ A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) ∧
    A ∪ A = A ∧ A ∩ A = A ∧
    (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ ∧ (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  constructor
  · -- Proof of Commutativity of ∪
    ext x 
    simp [Set.mem_union]
    <;> tauto 
  constructor 
  · -- Proof of Commutativity of ∩
    ext x 
    simp [Set.mem_inter]
    <;> tauto 
  constructor 
  · -- Proof of Associativity of ∪
    ext x 
    simp [Set.mem_union]
    <;> tauto 
  constructor 
  · -- Proof of Associativity of ∩
    ext x 
    simp [Set.mem_inter]
    <;> tauto 
  constructor
  · -- Proof of Distributivity of ∩ over ∪ 
    ext x 
    simp [Set.mem_inter, Set.mem_union]
    <;> tauto 
  constructor 
  · -- Proof of Distributivity of ∪ over ∩ 
    ext x 
    simp [Set.mem_union, Set.mem_inter]
    <;> tauto 
  constructor
  · -- Proof of Idempotence of ∪ 
    ext x 
    simp 
  constructor 
  · -- Proof of Idempotence of ∩ 
    ext x 
    simp 
  constructor 
  · -- Proof of De Morgan's Law for ∪ 
    ext x 
    simp [Set.mem_compl, Set.mem_union]
    <;> tauto 
  · -- Proof of De Morgan's Law for ∩ 
    ext x 
    simp [Set.mem_compl, Set.mem_inter]
    <;> tauto