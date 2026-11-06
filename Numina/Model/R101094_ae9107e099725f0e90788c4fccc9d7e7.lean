import Mathlib

theorem number_theory_274369 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ n + 297 = (n % 10) * 100 + ((n / 10) % 10) * 10 + ((n / 100))} = 60 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ n + 297 = (n % 10) * 100 + ((n / 10) % 10) * 10 + ((n / 100))} = Finset.filter (fun n => n + 297 = (n % 10) * 100 + ((n / 10) % 10) * 10 + ((n / 100))) (Finset.Icc 100 999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide