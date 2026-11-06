import Mathlib

theorem number_theory_285821 :
  {i : ℕ | 0 < i ∧ i < 1001 
  ∧ ((¬ 2 ∣ i ∧ ¬ 3 ∣ i ∧ ¬ 5 ∣ i) ∨ (¬ 2 ∣ i ∧ 3 ∣ i ∧ 5 ∣ i) ∨ (2 ∣ i ∧ ¬ 3 ∣ i ∧ 5 ∣ i) ∨ (2 ∣ i ∧ 3 ∣ i ∧ ¬ 5 ∣ i) )}.ncard = 499 := by
  have h1 : {i : ℕ | 0 < i ∧ i < 1001 
      ∧ ((¬ 2 ∣ i ∧ ¬ 3 ∣ i ∧ ¬ 5 ∣ i) ∨ (¬ 2 ∣ i ∧ 3 ∣ i ∧ 5 ∣ i) ∨ (2 ∣ i ∧ ¬ 3 ∣ i ∧ 5 ∣ i) ∨ (2 ∣ i ∧ 3 ∣ i ∧ ¬ 5 ∣ i) )
  } = Finset.filter (fun i => 0 < i ∧ i < 1001 
      ∧ ((¬ 2 ∣ i ∧ ¬ 3 ∣ i ∧ ¬ 5 ∣ i) ∨ (¬ 2 ∣ i ∧ 3 ∣ i ∧ 5 ∣ i) ∨ (2 ∣ i ∧ ¬ 3 ∣ i ∧ 5 ∣ i) ∨ (2 ∣ i ∧ 3 ∣ i ∧ ¬ 5 ∣ i) )
    ) (Finset.Icc 0 1001) := by
    ext i
    simp
    <;> omega

  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide