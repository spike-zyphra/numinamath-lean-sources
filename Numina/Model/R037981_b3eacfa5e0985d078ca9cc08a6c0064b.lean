import Mathlib

theorem number_theory_96759 :
    let S : ℕ → ℕ := fun n ↦ (Nat.digits 10 n).sum
    {n | n > 0 ∧ n + S n + S (S n) = 2007}.ncard = 4 := by 
  intro S 
  have h1 : {n | n > 0 ∧ n + S n + S (S n) = 2007} = Finset.filter (fun n => n > 0 ∧ n + S n + S (S n) = 2007) (Finset.Iic 2007) := by
    ext n 
    simp 
    intro h1 h2
    have h4 : n ≤ 2007 := by 
      omega 
    tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide