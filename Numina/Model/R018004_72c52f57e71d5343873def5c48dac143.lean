import Mathlib

theorem number_theory_160666 :
    Set.ncard {x : ℕ | 0 < x ∧ x < 100 ∧ Nat.Prime (3^x + 5^x + 7^x + 11^x + 13^x + 17^x + 19^x)} = 0 := by
  have h1 : {x : ℕ | 0 < x ∧ x < 100 ∧ Nat.Prime (3^x + 5^x + 7^x + 11^x + 13^x + 17^x + 19^x)} = Finset.filter (fun x : ℕ => 0 < x ∧ x < 100 ∧ Nat.Prime (3^x + 5^x + 7^x + 11^x + 13^x + 17^x + 19^x)) (Finset.Icc 0 100) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide