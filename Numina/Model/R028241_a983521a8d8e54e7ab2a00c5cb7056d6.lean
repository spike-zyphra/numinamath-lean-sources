import Mathlib

open Real

theorem algebra_139230 : ⌊∑ i ∈ Finset.range 2016, sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2)⌋ = 2016 := by 
  have h1 : ∀ (i : ℕ), sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2) = 1 + 1 / ((i + 1) * (i + 2)) := by
    intro i
    have h2 : (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2 : ℝ) = (1 + 1 / ((i + 1) * (i + 2)) : ℝ)^2 := by 
      field_simp 
      ring
    have h3 : sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2 : ℝ) = 1 + 1 / ((i + 1) * (i + 2)) := by 
      rw [h2]
      have h4 : 0 ≤ (1 + 1 / ((i + 1) * (i + 2) : ℝ)) := by 
        positivity
      rw [Real.sqrt_sq (h4)]
    exact h3 
  have hsum : ∑ i in Finset.range 2016, sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2) = (2017 - 1/2017 : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    have h2 : ∀ n : ℕ, ∑ i in Finset.range n, (1 + 1 / ((i + 1) * (i + 2)) : ℝ) = (n + 1 - 1 / (n + 1 : ℝ) : ℝ) := by
      intro n 
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp 
        ring
    have eq1 := h2 2016 
    have eq2 : ∑ i in Finset.range 2016, (1 + 1 / ((i + 1) * (i + 2)) : ℝ) = (2017 - 1/2017 : ℝ) := by
      rw [eq1]
      norm_num 
    exact_mod_cast eq2 
  rw [hsum]
  norm_num [Int.floor_eq_iff]