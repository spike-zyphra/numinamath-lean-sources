import Mathlib

def is_white_tiger (n : ℕ) := 6 ∣ n ∧ (Nat.digits 10 n).sum = 6

theorem number_theory_218217 :
    Set.ncard {n | n ∈ Finset.Icc 1 2022 ∧ is_white_tiger n} = 30 := by
  have h1 : {n | n ∈ Finset.Icc 1 2022 ∧ is_white_tiger n} = Finset.filter (fun n => 6 ∣ n ∧ (Nat.digits 10 n).sum = 6) (Finset.Icc 1 2022) := by
    ext n
    simp [is_white_tiger]
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide