import Mathlib

theorem number_theory_263845 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 1000 ∧ 4 ∣ n ∧ ¬(3 ∣ n) ∧ ¬(10 ∣ n)} = 133 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 1000 ∧ 4 ∣ n ∧ ¬(3 ∣ n) ∧ ¬(10 ∣ n)} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 1000 ∧ 4 ∣ n ∧ ¬(3 ∣ n) ∧ ¬(10 ∣ n)) (Finset.Icc 0 1000) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide