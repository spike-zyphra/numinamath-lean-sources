import Mathlib

open Finset

theorem number_theory_317841 {p : ℕ → ℕ → ℕ}
    (hp : ∀ n k, p n k = {x | x ∣ n ∧ x ≥ k}.ncard) :
    ∑ i ∈ Icc 1001 2000, p i (i - 1000) = 2000 := by 
  rw [sum_congr rfl fun i hi => hp i (i - 1000)]
  have h1 : ∑ i ∈ Icc 1001 2000, {x | x ∣ i ∧ x ≥ i - 1000}.ncard = 2000 := by 
    have h3 : ∑ i ∈ Icc 1001 2000, {x | x ∣ i ∧ x ≥ i - 1000}.ncard = 
            ∑ i ∈ Icc 1001 2000, 
              ( (Finset.filter (fun x => x ∣ i ∧ x ≥ i - 1000) (Finset.Icc (0 : ℕ) i)).card ) := by 
      apply sum_congr 
      . rfl 
      . intro i hi 
        have h4 : {x | x ∣ i ∧ x ≥ i - 1000} = (Finset.filter (fun x => x ∣ i ∧ x ≥ i - 1000) (Finset.Icc (0 : ℕ) i)) := by 
          ext x 
          simp at *
          intro hx1 hx2
          -- We know that if x divides i, then x <= i (if i > 0)
          have hx3 : x ≤ i := by 
            have hx4 : x ∣ i := hx1
            exact Nat.le_of_dvd (by omega) hx4
          all_goals 
            omega 
        rw [h4] 
        rw [Set.ncard_coe_Finset]
        all_goals try { tauto }
        all_goals try { linarith }
    rw [h3] 
    native_decide 
  exact h1