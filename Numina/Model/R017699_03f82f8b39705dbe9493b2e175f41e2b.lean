import Mathlib

theorem algebra_2385 {a : ℕ → ℝ} {d : ℝ} (h : ∀ n, a n = a 0 + d * n)
    (h1 : ∑ i in Finset.range 100, a i = 100) (h2 : ∑ i in Finset.range 100, a (i + 100) = 200) :
    d = 1 / 100 := by

  have eq1 : ∑ i in Finset.range 100, a i = 100 * a 0 + d * (4950 : ℝ) := by
    have h3 : ∀ i, i ∈ Finset.range 100 → a i = a 0 + d * (i : ℝ) := by 
      intro i hi
      specialize h i
      simpa using h 
    have h3' : ∑ i in Finset.range 100, a i = ∑ i in Finset.range 100, (a 0 + d * (i : ℝ)) := by
      apply Finset.sum_congr 
      · rfl 
      · intro i hi
        apply h3 i hi 
    rw [h3']
    have h4 : ∑ i in Finset.range 100, (a 0 + d * (i : ℝ)) = 100 * a 0 + d * (4950 : ℝ) := by 
      simp only [Finset.sum_range_succ, add_mul, mul_add]
      norm_num
      <;> ring 
    exact h4

  have eq2 : ∑ i in Finset.range 100, a (i + 100) = 100 * a 0 + d * (14950 : ℝ) := by
    have h3 : ∀ i, i ∈ Finset.range 100 → a (i + 100) = a 0 + d * ((i + 100 : ℝ)) := by
      intro i hi 
      specialize h (i + 100)
      simpa using h 
    have h3' : ∑ i in Finset.range 100, a (i + 100) = ∑ i in Finset.range 100, (a 0 + d * ((i + 100 : ℝ)) ) := by 
      apply Finset.sum_congr 
      · rfl 
      · intro i hi 
        apply h3 i hi 
    rw [h3']
    have h4 : ∑ i in Finset.range 100, (a 0 + d * ((i + 100 : ℝ)) ) = 100 * a 0 + d * (14950 : ℝ) := by
      simp only [Finset.sum_range_succ, add_mul, mul_add]
      norm_num 
      <;> ring
    exact h4
  
  rw [eq1] at h1 
  rw [eq2] at h2
  
  linarith