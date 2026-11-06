import Mathlib

theorem number_theory_151784 :
    {n : ℕ | Odd n ∧ n < 10000 ∧ n < (n ^ 9) % 10000}.encard =
    {n : ℕ | Odd n ∧ n < 10000 ∧ n > (n ^ 9) % 10000}.encard := by
  have h1 : {n : ℕ | Odd n ∧ n < 10000 ∧ n < (n ^ 9) % 10000} = Finset.filter (fun n => Odd n ∧ n < 10000 ∧ n < (n ^ 9) % 10000) (Finset.Icc 0 9999) := by
    ext n
    simp [Nat.odd_iff]
    omega
  have h2 : {n : ℕ | Odd n ∧ n < 10000 ∧ n > (n ^ 9) % 10000} = Finset.filter (fun n => Odd n ∧ n < 10000 ∧ n > (n ^ 9) % 10000) (Finset.Icc 0 9999) := by
    ext n
    simp [Nat.odd_iff]
    omega
  rw [h1, h2]
  rw [Set.encard_coe_eq_coe_finsetCard]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide