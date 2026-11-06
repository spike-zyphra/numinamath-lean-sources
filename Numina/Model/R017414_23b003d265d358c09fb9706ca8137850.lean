import Mathlib

open Real
open scoped BigOperators

theorem inequalities_603096 {n : ℕ} (x : Fin n → ℝ)
  (h₀ : ∏ i : Fin n, x i = 1) (h₁ : ∀ i : Fin n, 0 ≤ x i) :
  ∑ i : Fin n, x i ≥ n := by
  have h13 : ∀ i : Fin n, 0 < x i := by 
    intro i 
    by_contra h 
    push_neg at h 
    have h14 : x i = 0 := by linarith [h₁ i, h]
    have h5 : ∏ i : Fin n, x i = 0 := by 
      have h6 : ∃ i : Fin n, x i = 0 := by 
        exact ⟨i, h14⟩ 
      rcases h6 with ⟨j, hj⟩ 
      have h7 : ∏ i : Fin n, x i = 0 := by
        apply Finset.prod_eq_zero_iff.mpr 
        exact ⟨j, by simpa using hj⟩ 
      linarith 
    linarith [h5, h₀]
  have h15 : ∑ i : Fin n, x i ≥ (n : ℝ) := by
    have h6 : ∑ i : Fin n, Real.log (x i) = (0 : ℝ) := by 
      have h7 : Real.log (∏ i : Fin n, x i) = ∑ i : Fin n, Real.log (x i) := by
        rw [Real.log_prod]
        intro i hi 
        have h18 : x i > 0 := h13 i 
        have h17 : x i > 0 := h13 i 
        linarith [h₁ i]
      have h8 : Real.log (∏ i : Fin n, x i) = (0 : ℝ) := by 
        rw [h₀] 
        norm_num 
      have h9 : ∑ i : Fin n, Real.log (x i) = (0 : ℝ) := by 
        linarith [h7, h8]
      exact_mod_cast h9 
    have h7 : ∀ i : Fin n, Real.log (x i) ≤ x i - (1 : ℝ) := by 
      intro i 
      have h10 : Real.log (x i) ≤ x i - (1 : ℝ) := by 
        have h11 : x i >0 := h13 i 
        have h12 : Real.log (x i) ≤ x i - (1 : ℝ) := by 
          linarith [Real.log_le_sub_one_of_pos (show (x i : ℝ) > 0 by linarith)]
        linarith 
      exact_mod_cast h10 
    have h8 : ∑ i : Fin n, (Real.log (x i)) ≤ ∑ i : Fin n, (x i - (1 : ℝ)) := by 
      apply Finset.sum_le_sum 
      intro i hi 
      have h14 : Real.log (x i) ≤ x i -1 := by 
        specialize h7 i 
        linarith [h7] 
      linarith 
    -- Now rewrite it at the endpoints. From $\ln (x_i) \le x_i -1, and sum over i=0 \le ...$
    have h12 : ∑ i : Fin n, x i - (↑n : ℝ) ≥ (0 : ℝ) := by 
      have h35 : ∑ i : Fin n, (x i - (1 : ℝ)) = (∑ i : Fin n, x i) - (↑n : ℝ) := by 
        simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
        <;> ring 
      have h36 : ∑ i : Fin n, (x i - (1 : ℝ)) ≥ (0 : ℝ) := by
        linarith [h6, h8, h35] 
      linarith 
    linarith 
  linarith