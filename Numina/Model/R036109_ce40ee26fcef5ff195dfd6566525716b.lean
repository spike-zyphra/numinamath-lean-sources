import Mathlib

theorem number_theory_79336 :
    ∃ m n : ℕ, m.Coprime n ∧ (m / n : ℚ) = {c : ℤ | 70 ∣ c ∧ c ∣ 630000}.ncard / 630000 := by 
  use 2, 13125
  constructor
  · -- Show that 2 and 13125 are coprime
    norm_num [Nat.Coprime]
  · -- Show that (2/13125 : ℚ) = (96 : ℚ)/630000
    have h1 : {c : ℤ | 70 ∣ c ∧ c ∣ 630000}.ncard = 96 := by 
      have h2 : {c : ℤ | 70 ∣ c ∧ c ∣ 630000} = Finset.filter (fun c : ℤ => 70 ∣ c ∧ c ∣ 630000) (Finset.Icc (-630000 : ℤ) (630000 : ℤ)) := by 
        ext c
        simp
        intro h1 h2
        have h3 : c ≤ 630000 := by 
          exact Int.le_of_dvd (by norm_num) h2
        have h4 : -630000 ≤ c := by
          have h5 : -c ∣ 630000 := by 
            exact Int.neg_dvd.2 h2
          have h6 : -c ≤ 630000 := by 
            exact Int.le_of_dvd (by norm_num) h5
          omega
        tauto
      rw [h2]
      rw [Set.ncard_coe_Finset]
      native_decide
    norm_num [h1]