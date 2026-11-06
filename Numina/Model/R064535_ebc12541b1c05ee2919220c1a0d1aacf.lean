import Mathlib

def isOddSumNumber (n : ℕ) : Prop :=
  Odd (n + (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100))) ∧
  ∀ d ∈ Nat.digits 10 (n + (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100))), Odd d

theorem number_theory_324900 :
    Set.ncard {n | n ∈ Finset.Icc 100 999 ∧ isOddSumNumber n} = 100 := by
  have h1 : {n | n ∈ Finset.Icc 100 999 ∧ isOddSumNumber n} = Finset.filter (fun n => Odd (n + (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100))) ∧ ∀ d ∈ Nat.digits 10 (n + (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100))), Odd d) (Finset.Icc 100 999) := by
    ext n
    simp [isOddSumNumber]
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide