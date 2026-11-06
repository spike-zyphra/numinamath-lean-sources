import Mathlib

theorem algebra_128878 (S : Finset ℝ) (hS : S.card = 60)
    (hS1 : ∑ x ∈ S, (x + 3)^2 = ∑ x ∈ S, x^2) :
    ∑ x ∈ S, (x + 4)^2 - ∑ x ∈ S, x^2 = 240 := by
  have eq1 : ∑ x in S, (x + 3) ^ 2 = ∑ x in S, x^2 := by 
    simpa using hS1

  have eq2 : ∑ x in S, (x + 3) ^ 2 = ∑ x in S, x^2 + 6 * (∑ x in S, x) + (9 * (S.card : ℝ)) := by
    have h1 : ∑ x in S, (x + 3) ^ 2 = ∑ x in S, (x^2 + 6 * x + 9) := by 
      apply Finset.sum_congr
      · rfl
      · intro x hx
        ring
    rw [h1]
    have h2 : ∑ x in S, (x^2 + 6 * x + 9) = ∑ x in S, x^2 + 6 * (∑ x in S, x) + (9 * (S.card : ℝ)) := by 
      simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add]
      <;> ring 
    rw [h2]
  
  have eq3 : 6 * (∑ x in S, x) + (9 * (S.card : ℝ)) = 0 := by 
    linarith [eq1, eq2]

  have eq4 : (S.card : ℝ) = 60 := by 
    exact_mod_cast hS

  have eq5 : ∑ x in S, x = -90 := by 
    rw [eq4] at eq3
    linarith
  
  have eq6 : ∑ x in S, (x + 4) ^ 2 = ∑ x in S, x^2 + 8 * (∑ x in S, x) + (16 * (S.card : ℝ)) := by 
    have h1 : ∑ x in S, (x + 4) ^ 2 = ∑ x in S, (x^2 + 8 * x + 16) := by
      apply Finset.sum_congr 
      · rfl 
      · intro x hx
        ring 
    rw [h1]
    have h2 : ∑ x in S, (x^2 + 8 * x + 16) = ∑ x in S, x^2 + 8 * (∑ x in S, x) + (16 * (S.card : ℝ)) := by 
      simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add]
      <;> ring 
    rw [h2]
  
  calc 
    ∑ x in S, (x + 4) ^ 2 - ∑ x in S, x^2 = (∑ x in S, x^2 + 8 * (∑ x in S, x) + (16 * (S.card : ℝ))) - ∑ x in S, x^2 := by 
      rw [eq6]
    _ = 8 * (∑ x in S, x) + (16 * (S.card : ℝ)) := by 
      linarith 
    _ = 8 * (-90) + (16 * (60 : ℝ)) := by 
      rw [eq5, eq4]
    _ = (240 : ℝ) := by 
      norm_num