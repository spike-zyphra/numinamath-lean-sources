import Mathlib

theorem number_theory_295158 : {a : ℕ | 1 ≤ a ∧ a ≤ 1000 ∧ 4 ∣ (a ^ 2 + 1) * (a ^ 2 + 5)}.encard = 500 := by 
  have h1 : {a : ℕ | 1 ≤ a ∧ a ≤ 1000 ∧ 4 ∣ (a ^ 2 + 1) * (a ^ 2 + 5)} = Finset.filter (fun a => 1 ≤ a ∧ a ≤ 1000 ∧ 4 ∣ (a ^ 2 + 1) * (a ^ 2 + 5)) (Finset.Icc 0 1000) := by
    ext a
    simp
    <;> omega
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try native_decide
  <;> try omega