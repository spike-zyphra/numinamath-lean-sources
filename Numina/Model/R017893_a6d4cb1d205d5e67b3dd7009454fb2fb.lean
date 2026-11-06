import Mathlib

theorem number_theory_59953 :
    Set.ncard {n : ℕ | n > 0 ∧ n ≤ 1991 ∧ 6 ∣ (n ^ 2 + 3 * n + 2)} = 1328 := by
  have h1 : {n : ℕ | n > 0 ∧ n ≤ 1991 ∧ 6 ∣ (n ^ 2 + 3 * n + 2)} = Finset.filter (fun n : ℕ => n > 0 ∧ n ≤ 1991 ∧ 6 ∣ (n ^ 2 + 3 * n + 2)) (Finset.Icc 0 1991) := by
    ext n 
    simp 
    omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide