import Mathlib

theorem number_theory_5414 :
    {n : ℕ | n ∈ Finset.Icc 1 2000 ∧ ¬(10 ∣ n) ∧ ¬(14 ∣ n) ∧ ¬(21 ∣ n)}.ncard = 1638 := by
        have h1 : {n : ℕ | n ∈ Finset.Icc 1 2000 ∧ ¬(10 ∣ n) ∧ ¬(14 ∣ n) ∧ ¬(21 ∣ n)} = Finset.filter (fun n => ¬(10 ∣ n) ∧ ¬(14 ∣ n) ∧ ¬(21 ∣ n)) (Finset.Icc 1 2000) := by
            ext n
            simp
        rw [h1]
        rw [Set.ncard_coe_Finset]
        native_decide