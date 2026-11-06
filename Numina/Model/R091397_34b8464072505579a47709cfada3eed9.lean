import Mathlib

theorem number_theory_134819 :
    {x : ℕ | x ∈ Finset.Icc 100 999 ∧ 3 ∣ x ∧ Nat.gcd 15 (Nat.gcd x 20) = 5}.encard = 60 := by 
  have h1 : {x : ℕ | x ∈ Finset.Icc 100 999 ∧ 3 ∣ x ∧ Nat.gcd 15 (Nat.gcd x 20) = 5} = Finset.filter (fun x => 3 ∣ x ∧ Nat.gcd 15 (Nat.gcd x 20) = 5) (Finset.Icc 100 999) := by
    ext x
    simp
    all_goals tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide