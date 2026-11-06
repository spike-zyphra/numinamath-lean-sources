import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_311817 (n : ℕ) (f : Fin n → ℂ) :
  ∏ i : Fin n, (abs (f i)) * (exp (I * (arg (f i)))) =
  (∏ i : Fin n, (abs (f i))) * (exp (I * (∑ i : Fin n, (arg (f i))))) := by
  have h3 : ∀ (n : ℕ) (f : Fin n → ℂ),
      ∏ i : Fin n, (abs (f i)) * (exp (I * (arg (f i)))) =
      (∏ i : Fin n, (abs (f i))) * (exp (I * (∑ i : Fin n, (arg (f i))))) := by
    intro n f
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
      rw [ih (fun i : Fin n => f i.castSucc)]
      simp [Complex.exp_add, mul_add, mul_assoc]
      all_goals ring_nf <;> norm_num [Complex.ext_iff]
  specialize h3 n f
  simpa using h3