import Mathlib
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic    
import Mathlib.Tactic.SimpRw       
import Mathlib.Tactic.NormNum      

/--
The average age of 33 fifth-graders is 11.
The average age of 55 of their parents is 33.
What is the average age of all these parents and fifth-graders?

(A) 22, (B) 23.25, (C) 24.75, (D) 26.25, (E) 28
-/

theorem algebra_94533
    (fifth_graders : Fin 33 → ℕ)
    (parents : Fin 55 → ℕ)
    (h₀ : ∀ i, fifth_graders i = 11)
    (h₁ : ∀ i, parents i = 33)
    : ( Finset.univ.sum (fun i : Fin 33 => (fifth_graders i : ℝ))
      + Finset.univ.sum (fun i : Fin 55 => (parents i : ℝ)) )
      / ((33 : ℝ) + (55 : ℝ))
      = 24.75 := by
    -- First, we sum fifth-graders' ages
  have sum_fifth_graders :
    Finset.univ.sum (fun i : Fin 33 => (fifth_graders i : ℝ)) = 33 * 11 := by
    -- Now, we rewrite each term to 11, then sums up 33 times.
    simp_rw [h₀, Nat.cast_ofNat, Finset.sum_const, Finset.card_fin]
    -- We convert n•x to n*x, and reorder the factors  
    rw [nsmul_eq_mul]  
    ring
    -- Second, we sum of the parents' ages
  have sum_parents :
    Finset.univ.sum (fun i : Fin 55 => (parents i : ℝ)) = 55 * 33 := by
    simp_rw [h₁, Nat.cast_ofNat, Finset.sum_const, Finset.card_fin]
    rw [nsmul_eq_mul]
    ring
    -- Finally, we substitute the sums back into the main expression.
  rw [sum_fifth_graders, sum_parents]
  norm_num