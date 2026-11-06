import Mathlib

open Real Finset

theorem Inequalities_98998 (n : ℕ) {C : ℝ} (hc : C > 0) (hn : 0 < n) (a : ℕ → ℝ) (apos : ∀ i, 0 < a i) (hsum : ∑ i ∈ range n, a i = C) :
  ((∑ i ∈ range n, a i ) / (n : ℝ) ≥ (∏ i ∈ range n, a i) ^ (1 / (n : ℝ))) ∧ 
  ((∑ i ∈ range n, a i ) / (n : ℝ) = (∏ i ∈ range n, a i) ^ (1 / (n : ℝ)) → (∀ (i j : Fin n), a i = a j))
  := by 
  constructor
  · -- proving the inequalities
    have aux : (n : ℝ) = ∑ i ∈ range n, 1  := by 
      simp_all [Finset.sum_const]
    rw [aux, one_div] -- substitute `n` with sum of ones over reals.
    let w : ℕ → ℝ := fun k => 1
    calc 
      _ = (∏ i ∈ range n, a i ^ w i) ^ (∑ i ∈ range n, (w i : ℝ))⁻¹ := by 
        unfold w
        simp
      _ ≤ (∑ i ∈ range n, w i * a i) / ∑ i ∈ range n, w i := by 
        refine Real.geom_mean_le_arith_mean (range n) w a ?_ ?_ ?_
        intro i hi
        unfold w
        norm_num
        unfold w
        norm_num
        exact hn
        intro i hi
        linarith [apos i]
      _ = _ := by 
        simp [w]
  · -- equal condition
    intro h
    have aux : (∑ i ∈ range n, ((1 / (n : ℝ))) * a i)  = (∏ i ∈ range n, a i ^
      (1 / (n : ℝ))) := by 
      calc 
        _ = (∑ i ∈ range n, a i ) / (n : ℝ)  := by 
          simp
          rw [←Finset.mul_sum]
          ring
        _ = _ := by 
          rw [h]
          refine Eq.symm (finset_prod_rpow (range n) a ?_ (1 / (n : ℝ)))
          intro i hi
          linarith [apos i]
    intro i j
    let w : ℕ → ℝ := fun x => 1 / (n : ℝ)
    have eq : ∀ j ∈ range n, w j ≠ 0 → a j = ∑ i ∈ range n, w i * a i := by 
      refine (Real.geom_mean_eq_arith_mean_weighted_iff (range n) w a ?_ ?_ ?_).mp ?_
      intro i hi
      unfold w
      norm_num
      unfold w
      simp
      refine IsUnit.mul_inv_cancel ?_
      simp
      linarith
      intro i hi
      linarith [apos i]
      unfold w
      exact Eq.symm aux
    obtain hj := j.isLt
    have wjneq : w j ≠ 0 := by  
      unfold w
      norm_num
      linarith
    obtain eq_aux := eq j (by simp [hj]) wjneq
    unfold w at eq_aux
    rw [←mul_sum] at eq_aux
    obtain hi := i.isLt
    have wineq : w i ≠ 0 := by  
      unfold w
      norm_num
      linarith
    obtain eq_aux' := eq i (by simp [hi]) wineq
    unfold w at eq_aux'
    rw [←mul_sum] at eq_aux'
    rw [eq_aux, eq_aux']