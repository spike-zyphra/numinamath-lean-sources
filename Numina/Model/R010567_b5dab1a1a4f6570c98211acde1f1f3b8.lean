import Mathlib
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic    
import Mathlib.Tactic.SimpRw       
import Mathlib.Tactic.NormNum      

theorem algebra_94533
    (fifth_graders : Fin 33 → ℕ)
    (parents : Fin 55 → ℕ)
    (h₀ : ∀ i, fifth_graders i = 11)
    (h₁ : ∀ i, parents i = 33)
    : ( Finset.univ.sum (fun i : Fin 33 => (fifth_graders i : ℝ))
      + Finset.univ.sum (fun i : Fin 55 => (parents i : ℝ)) )
      / ((33 : ℝ) + (55 : ℝ))
      = 24.75 := by
  have h2 : Finset.univ.sum (fun i : Fin 33 => (fifth_graders i : ℝ)) = (33 : ℝ) * 11 := by
    simp [Finset.sum_const, Finset.card_univ, h₀]
    <;> norm_num
  have h3 : Finset.univ.sum (fun i : Fin 55 => (parents i : ℝ)) = (55 : ℝ) * 33 := by
    simp [Finset.sum_const, Finset.card_univ, h₁]
    <;> norm_num
  rw [h2, h3]
  norm_num