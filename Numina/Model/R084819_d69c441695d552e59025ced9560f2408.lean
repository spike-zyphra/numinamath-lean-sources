import Mathlib

theorem algebra_13388 :
    (Finset.Icc 10000 99999).card = 90000 ∧
    {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ n % 10 < 5}.ncard = 45000 := by
  have h1 : (Finset.Icc 10000 99999).card = 90000 := by 
    native_decide

  have h2 : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ n % 10 < 5}.ncard = 45000 := by
    have : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ n % 10 < 5} = Finset.filter (fun n => n % 10 < 5) (Finset.Icc 10000 99999) := by
      ext n
      simp
    rw [this]
    rw [Set.ncard_coe_Finset]
    native_decide
  
  constructor
  · exact h1
  · exact h2