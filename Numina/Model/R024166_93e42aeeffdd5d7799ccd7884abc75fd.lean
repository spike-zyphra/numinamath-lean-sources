import Mathlib

def is_pretty (n : ℕ) : Prop :=
  n ∈ Finset.Icc 1000 9999 ∧ (n % 10) = (Nat.digits 10 (n / 10)).prod

theorem number_theory_251592 : {n | is_pretty n}.encard = 215 := by 
  have h1 : {n | is_pretty n} = Finset.filter (fun n => (n % 10) = (Nat.digits 10 (n / 10)).prod) (Finset.Icc 1000 9999) := by
    ext n
    simp [is_pretty]
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide