import Mathlib

def is_special_prime (n : ℕ) : Prop :=
  Nat.Prime n ∧ Nat.Prime (10 * (n % 10) + (n / 10))

theorem number_theory_1289 :
    Set.ncard {n | n ∈ Finset.Icc 10 99 ∧ is_special_prime n} = 9 := by
  have h1 : {n | n ∈ Finset.Icc 10 99 ∧ is_special_prime n} = Finset.filter (fun n => Nat.Prime n ∧ Nat.Prime (10 * (n % 10) + (n / 10))) (Finset.Icc 10 99) := by
    ext n
    simp [is_special_prime]
    all_goals tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide