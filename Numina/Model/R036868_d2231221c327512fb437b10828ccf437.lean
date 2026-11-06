import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_22431 :
  IsLeast {∑ i : Fin 12, (a i)^2 | (a : Fin 12 → ℝ) (h : ∑ i : Fin 12, a i = 1)} (1 / 12) := by
  constructor
  · -- Show 1/12 achieves the bound
    use (fun i => (1 / 12 : ℝ))
    constructor
    · -- Show ∑ i : Fin 12, (fun i => (1 / 12 : ℝ)) i = 1
      norm_num [Finset.sum_const, Finset.card_univ]
    · -- Show ∑ i : Fin 12, (fun i => (1 / 12 : ℝ)) i ^ 2 = 1 / 12
      norm_num [Finset.sum_const, Finset.card_univ]
  · -- Show that 1/12 is minimal 
    intro B hB
    rcases hB with ⟨a, ha, hB⟩
    have h1 : ∑ i : Fin 12, (a i) = (1 : ℝ) := ha
    have h2 : ∑ i : Fin 12, (a i ^ 2) ≥ (1 / 12 : ℝ) := by 
      have h3 : ∑ i : Fin 12, (a i - (1 / 12)) ^ 2 ≥ (0 : ℝ) := by 
        apply Finset.sum_nonneg 
        intro i hi 
        have : (a i - (1 / 12)) ^ 2 ≥ (0 : ℝ) := by 
          apply sq_nonneg 
        exact_mod_cast this 
      have h4 : ∑ i : Fin 12, (a i - (1 / 12)) ^ 2 = 
        ∑ i : Fin 12, (a i ^ 2 : ℝ) - 2 * (1 / 12 : ℝ) * (∑ i : Fin 12, (a i : ℝ)) + 12 * ((1 / 12 : ℝ) ^ 2 : ℝ) := by 
        simp [Finset.sum, sub_sq]
        <;> ring
      rw [h4] at h3 
      rw [h1] at h3 
      norm_num at h3 ⊢ 
      linarith 
    linarith [hB, h2]