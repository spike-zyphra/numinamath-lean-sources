import Mathlib

theorem algebra_275649 (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hsum : ∑ i, |x i| = 2005 + |∑ i, x i|) :
    n ≥ 2006 := by 
  by_contra h 
  push_neg at h 
  have h1 : n ≤ 2005 := by 
    omega 
  have h2 : ∑ i : Fin n, |x i| < (n : ℝ) := by 
    have h3 : ∀ i : Fin n, |x i| < 1 := hx 
    have h4 : ∑ i : Fin n, |x i| < ∑ i : Fin n, (1 : ℝ) := by 
      apply Finset.sum_lt_sum 
      · -- Show that for all i, |x i| ≤ 1 
        intro i hi 
        specialize h3 i 
        all_goals try linarith 
      · -- Show that there exists an i such that |x i| < 1 
        use ⟨0, by omega⟩ 
        simp [h3]
    have h5 : ∑ i : Fin n, (1 : ℝ) = (n : ℝ) := by 
      simp [Finset.sum_const]
    linarith [h4, h5]
  have h3' : (n : ℝ) ≤ (2005 : ℝ) := by 
    exact_mod_cast h1 
  have h4 : ∑ i : Fin n, |x i| ≥ (2005 : ℝ) := by 
    have h5 : ∑ i : Fin n, |x i| = 2005 + |∑ i : Fin n, x i| := by 
      linarith [hsum] 
    have h6 : |∑ i : Fin n, x i| ≥ 0 := abs_nonneg (∑ i : Fin n, x i) 
    linarith [h5, h6]
  have h5 : ∑ i : Fin n, |x i| < (2005 : ℝ) := by 
    have h6 : (n : ℝ) ≤ (2005 : ℝ) := h3' 
    have h7 : ∑ i : Fin n, |x i| < (n : ℝ) := h2 
    nlinarith 
  linarith [h4, h5]