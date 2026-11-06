import Mathlib

theorem number_theory_610205 : {n ∈ Finset.Ico (10 ^ 5) (10 ^ 6) | 27 ∣ n ∧ Nat.digits 10 n ⊆ {3, 6, 9}}.card = 51 := by
  have : {n ∈ Finset.Ico (10 ^ 5) (10 ^ 6) | 27 ∣ n ∧ Nat.digits 10 n ⊆ {3, 6, 9}} = Finset.filter (fun n => 27 ∣ n ∧ Nat.digits 10 n ⊆ {3, 6, 9}) (Finset.Ico (10 ^ 5) (10 ^ 6)) := by
    ext n
    simp
  rw [this]
  rw [Finset.filter]
  simp [Finset.Ico]
  <;> native_decide