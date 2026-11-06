import Mathlib

theorem number_theory_166967 :
    Set.ncard {n | n ∣ 256} = 9 ∧
    Set.ncard {n | n ∣ (2 * 256)} = 10 ∧
    Set.ncard {n | n ∣ (256 * 256)} = 17 := by
  have h₁ : {n | n ∣ 256} = Finset.filter (fun (x : ℕ) => x ∣ 256) (Finset.Iic 256) := by
    ext n
    simp
    intro h
    have h2 : n ≤ 256 := by 
      exact Nat.le_of_dvd (by norm_num) h
    omega
  have h₂ : {n | n ∣ (2 * 256)} = Finset.filter (fun (x : ℕ) => x ∣ (2 * 256)) (Finset.Iic (2 * 256)) := by
    ext n
    simp
    intro h
    have h2 : n ≤ 2 * 256 := by 
      exact Nat.le_of_dvd (by norm_num) h
    omega
  have h₃ : {n | n ∣ (256 * 256)} = Finset.filter (fun (x : ℕ) => x ∣ (256 * 256)) (Finset.Iic (256 * 256)) := by
    ext n
    simp
    intro h
    have h2 : n ≤ 256 * 256 := by 
      exact Nat.le_of_dvd (by norm_num) h
    omega
  have h4 : Set.ncard {n | n ∣ 256} = 9 := by
    rw [h₁]
    rw [Set.ncard_coe_Finset]
    native_decide
  have h5 : Set.ncard {n | n ∣ (2 * 256)} = 10 := by
    rw [h₂]
    rw [Set.ncard_coe_Finset]
    native_decide
  have h6 : Set.ncard {n | n ∣ (256 * 256)} = 17 := by
    rw [h₃]
    rw [Set.ncard_coe_Finset]
    native_decide
  exact ⟨h4, h5, h6⟩