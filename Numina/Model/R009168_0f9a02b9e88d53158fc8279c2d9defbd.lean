import Mathlib

theorem number_theory_12325 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ n % 100 = 45 ∧ 45 ∣ n} = 10 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ n % 100 = 45 ∧ 45 ∣ n} = Finset.filter (fun n => n % 100 = 45 ∧ 45 ∣ n) (Finset.Icc 1000 9999) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide