import Mathlib

theorem number_theory_63647 :
    Set.ncard {n : ℕ | n > 0 ∧ (n + 1) ∣ 2016} = 35 := by
  have h1 : {n : ℕ | n > 0 ∧ (n + 1) ∣ 2016} = Finset.filter (fun n => n > 0 ∧ (n + 1) ∣ 2016) (Finset.Iic 2015) := by
    ext n
    simp
    intro h1 h2
    have h3 : n + 1 ∣ 2016 := h2
    have h4 : n + 1 ≤ 2016 := by 
      exact Nat.le_of_dvd (by omega) h3
    have : n ≤ 2015 := by
      omega
    all_goals tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide