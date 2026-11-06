import Mathlib

theorem number_theory_94387 :
    Set.ncard {n : ℕ | 10 ≤ n ∧ n ≤ 50 ∧ n % (n % 10) = 0} = 17 := by 
  have : {n : ℕ | 10 ≤ n ∧ n ≤ 50 ∧ n % (n % 10) = 0} = Finset.toSet (Finset.filter (fun n => 10 ≤ n ∧ n ≤ 50 ∧ n % (n % 10) = 0) (Finset.range 51)) := by 
    ext n 
    simp 
    omega 
  rw [this] 
  rw [Set.ncard_coe_Finset] 
  native_decide