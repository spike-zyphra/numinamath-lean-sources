import Mathlib

def is_flippant (n : ℕ) : Prop :=
  n > 0 ∧ ¬(n % 10 = 0) ∧ 7 ∣ n ∧ 7 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))

theorem number_theory_191526 :
    Set.ncard {n | 10 ≤ n ∧ n < 1000 ∧ is_flippant n} = 17 := by 
  have h : {n | 10 ≤ n ∧ n < 1000 ∧ is_flippant n} = 
      Finset.filter (fun n => 10 ≤ n ∧ n < 1000 ∧ 
          n > 0 ∧ ¬(n % 10 = 0) ∧ 7 ∣ n ∧ 7 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) (Finset.Icc 0 1000) := by
    ext n
    simp [is_flippant]
    omega
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide