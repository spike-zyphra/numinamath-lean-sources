import Mathlib

def O (n : ℕ) := Odd (Nat.digits 10 n).sum

def E (n : ℕ) := Even (Nat.digits 10 n).sum

theorem number_theory_62776 :
    {n | O n ∧ n ∈ Finset.Icc 1 1000000}.ncard > {n | E n ∧ n ∈ Finset.Icc 1 1000000}.ncard := by
  have h1 : {n | O n ∧ n ∈ Finset.Icc 1 1000000} = Finset.filter (fun n => Odd (Nat.digits 10 n).sum) (Finset.Icc 1 1000000) := by
    ext n
    simp [O, E, Finset.mem_Icc]
    <;> tauto
  have h2 : {n | E n ∧ n ∈ Finset.Icc 1 1000000} = Finset.filter (fun n => Even (Nat.digits 10 n).sum) (Finset.Icc 1 1000000) := by
    ext n
    simp [O, E, Finset.mem_Icc]
    <;> tauto
  rw [h1, h2]
  rw [Set.ncard_coe_Finset]
  rw [Set.ncard_coe_Finset]
  native_decide