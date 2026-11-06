import Mathlib

theorem number_theory_295317 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 10000 ∧ 7 ∣ n ∧ ¬5 ∣ n} = 1143 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 10000 ∧ 7 ∣ n ∧ ¬5 ∣ n} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 10000 ∧ 7 ∣ n ∧ ¬5 ∣ n) (Finset.Icc 0 10000) := by
    ext n
    simp
    omega

  rw [h1] at *
  rw [Set.ncard_coe_Finset]
  native_decide