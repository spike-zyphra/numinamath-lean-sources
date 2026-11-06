import Mathlib

def is_hussel (n : ℕ) : Prop :=
  (Nat.digits 10 n).all (fun d => d ≠ 0) ∧
  n % 11 = 0 ∧ n % 12 = 0 ∧
  (Nat.digits 10 n).permutations.all (fun p => 12 ∣ Nat.ofDigits 10 p)

theorem number_theory_173904 :
    Set.ncard {n | n ∈ Finset.Icc 10000 99999 ∧ is_hussel n} = 2 := by
  have h1 : {n | n ∈ Finset.Icc 10000 99999 ∧ is_hussel n} = Finset.filter (fun n => 
    (Nat.digits 10 n).all (fun d => d ≠ 0) ∧
    n % 11 = 0 ∧ n % 12 = 0 ∧
    (Nat.digits 10 n).permutations.all (fun p => 12 ∣ Nat.ofDigits 10 p)
  ) (Finset.Icc 10000 99999) := by
    ext n
    simp [is_hussel]
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide