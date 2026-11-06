import Mathlib

theorem number_theory_102572 : {n : ℕ | n ∈ Finset.Icc 1 2013 ∧ (Nat.digits 10 n).sum = 9}.encard = 101 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 2013 ∧ (Nat.digits 10 n).sum = 9} = Finset.filter (fun n => (Nat.digits 10 n).sum = 9) (Finset.Icc 1 2013) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> native_decide