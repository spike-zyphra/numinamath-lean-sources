import Mathlib

theorem number_theory_165250 (A B : Finset ℕ) (hA : A = {1, 2019}) (hB : B = {1, 2020}) :
    ∃ x ∈ A, ∃ y ∈ B, x > 0 ∧ y > 0 ∧ Nat.Coprime x y ∧ x + y ∈ A ∪ B := by 
  rw [hA, hB]
  use 2019, by simp
  use 1, by simp
  all_goals simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Nat.coprime_one_right]
  <;> trivial
  <;> native_decide