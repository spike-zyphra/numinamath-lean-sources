import Mathlib

theorem algebra_21733 (n : ℕ) (hn : n > 0) (a : Fin n → ℝ)
    (h : ∑ i : Fin n, a i = ∑ i : Fin n, (a i)^2) :
    (∑ i : Fin n, a i) / n ≤ 1 := by
  have h1 : (∑ i : Fin n, (a i - 1) ^ 2) ≥ 0 := by 
    apply Finset.sum_nonneg 
    intro i hi 
    apply sq_nonneg 
  have h2 : (∑ i : Fin n, (a i - 1) ^ 2) = (∑ i : Fin n, (a i)^2) - 2 * (∑ i : Fin n, a i) + n := by 
    have eq3 : ∀ i : Fin n, (a i - 1) ^ 2 = (a i)^2 - 2 * (a i) + 1 := by 
      intro i 
      ring_nf 
    have eq4 : (∑ i : Fin n, (a i - 1) ^ 2) = (∑ i : Fin n, ((a i)^2 - 2 * (a i) + 1)) := by 
      apply Finset.sum_congr 
      · rfl 
      · intro i hi 
        exact_mod_cast eq3 i 
    have eq5 : (∑ i : Fin n, ((a i)^2 - 2 * (a i) + 1)) = (∑ i : Fin n, (a i)^2) - 2 * (∑ i : Fin n, a i) + n := by 
      simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ]
      <;> ring 
    linarith [eq4, eq5]
  rw [h] at h2 
  have h3 : (∑ i : Fin n, (a i - 1) ^ 2) = n - (∑ i : Fin n, a i) := by 
    nlinarith 
  have h4 : (∑ i : Fin n, a i) ≤ (n : ℝ) := by 
    nlinarith [h1, h3]
  have hn1 : (↑n : ℝ) > 0 := by exact_mod_cast show n > 0 by exact hn 
  have h6 : (∑ i : Fin n, a i) ≤ (n : ℝ) := by linarith [h4]
  have h7 : (∑ i : Fin n, a i) / (n : ℝ) ≤ 1 := by 
    have hx1 : (∑ i : Fin n, a i) / (n : ℝ) ≤ (n : ℝ) / (n : ℝ) := by 
      have hx2 : (↑n : ℝ) > 0 := by exact_mod_cast show n > 0 by exact hn 
      apply (div_le_div_right hx2).mpr 
      linarith 
    have h9 : (n : ℝ) / (n : ℝ) = 1 := by 
      field_simp 
    linarith [hx1, h9] 
  simpa using h7