import Mathlib

theorem number_theory_174124 : {n : ℕ | n < 1000 ∧ (Nat.digits 10 n).sum = 7}.encard = 36 := by
  have h1 : {n : ℕ | n < 1000 ∧ (Nat.digits 10 n).sum = 7} = Finset.filter (fun n => (Nat.digits 10 n).sum = 7) (Finset.Iio 1000) := by
    ext n
    simp
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide