import Mathlib

def isMagic (n : ℕ) : Prop :=
  (Nat.digits 10 n).length = 3 ∧ (Nat.digits 10 n).sum ≡ 0 [MOD 11]

theorem number_theory_6763 :
    Set.ncard {n | 100 ≤ n ∧ n < 1000 ∧ isMagic n} = 82 := by
  have h1 : {n | 100 ≤ n ∧ n < 1000 ∧ isMagic n} = Finset.filter (fun n => 100 ≤ n ∧ n < 1000 ∧ (Nat.digits 10 n).length = 3 ∧ (Nat.digits 10 n).sum ≡ 0 [MOD 11]) (Finset.Icc 0 999) := by
    ext n
    simp [isMagic]
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide