import Mathlib

open Real

theorem algebra_251005 (x : ℝ) (hx : 0 < x ∧ x ≠ 1) :
    ∑ i ∈ Finset.range 10, (1 / logb (5 ^ (i + 1)) x) = 55 / logb 5 x := by
  have hx1 : 0 < x := hx.1
  have hx2 : x ≠ 1 := hx.2
  have h : ∀ (k : ℕ), 1 / logb (5 ^ (k + 1)) x = (k + 1 : ℝ) / logb 5 x := by
    intro k
    have h1 : logb (5 ^ (k + 1)) x = log x / ((k + 1 : ℝ) * log (5 : ℝ)) := by
      have h2 : log (5 ^ (k + 1 : ℕ)) = (k + 1 : ℝ) * log (5 : ℝ) := by
        simp [log_pow]
      have h3 : logb (5 ^ (k + 1 : ℕ)) x = log x / log (5 ^ (k + 1 : ℕ)) := by 
        field_simp [logb]
      rw [h3, h2]
    have h4 : logb (5 : ℝ) x = log x / log (5 : ℝ) := by 
      field_simp [logb]
    rw [h1, h4]
    field_simp
    all_goals ring
  have h2 : ∑ i in Finset.range 10, (1 / logb (5 ^ (i + 1)) x) = ∑ i in Finset.range 10, ((i + 1 : ℝ) / logb 5 x) := by
    apply Finset.sum_congr
    · rfl
    intro i hi
    specialize h i
    simpa using h
  rw [h2]
  have h4 : ∑ i in Finset.range 10, ((i + 1 : ℝ) / logb 5 x) = (55 : ℝ) / logb 5 x := by
    have h5 : ∑ i in Finset.range 10, ((i + 1 : ℝ) / logb 5 x) = ( (∑ i in Finset.range 10, (i + 1 : ℝ)) ) / logb 5 x := by
      rw [Finset.sum_div]
    rw [h5]
    have h7 : ∑ i in Finset.range 10, ((i + 1 : ℝ)) = (55 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    rw [h7]
  linarith