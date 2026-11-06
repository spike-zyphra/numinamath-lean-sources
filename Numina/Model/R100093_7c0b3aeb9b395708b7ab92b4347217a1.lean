import Mathlib

theorem number_theory_160286 :
    Set.ncard {x : ℕ | 5 ∣ x ∧ 121 < x ∧ x < 1331 ∧ (Nat.digits 11 x).headI > (Nat.digits 11 x).tail.reverse.headI} = 99 := by
  have h1 : {x : ℕ | 5 ∣ x ∧ 121 < x ∧ x < 1331 ∧ (Nat.digits 11 x).headI > (Nat.digits 11 x).tail.reverse.headI} = Finset.filter (fun x => 5 ∣ x ∧ 121 < x ∧ x < 1331 ∧ (Nat.digits 11 x).headI > (Nat.digits 11 x).tail.reverse.headI) (Finset.Icc 0 1331) := by
    ext x
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide