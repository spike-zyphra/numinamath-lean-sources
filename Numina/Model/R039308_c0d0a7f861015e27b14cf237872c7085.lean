import Mathlib

open Real

theorem algebra_302428 :
    ⌊∑ i ∈ Finset.range 1999, sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2)⌋ = 1999 - 1 / 2000 := by
  have h1 : ∀ i : ℕ, sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2 : ℝ) = 1 + 1 / ((i + 1 : ℝ) * (i + 2)) := by 
    intro i
    have h2 : (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2 : ℝ) = (1 + 1 / ((i + 1) * (i + 2)) : ℝ) ^ 2 := by 
      field_simp
      ring_nf
    rw [h2]
    rw [Real.sqrt_sq]
    positivity
  have h3 : ∑ i in Finset.range 1999, sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2) = ∑ i in Finset.range 1999, (1 + 1 / ((i + 1 : ℝ) * (i + 2)) ) := by 
    apply Finset.sum_congr
    · rfl
    · intro i hi
      specialize h1 i
      simpa using h1
  rw [h3]
  have h4 : ∑ i in Finset.range 1999, (1 + 1 / ((i + 1 : ℝ) * (i + 2)) ) = 1999 + (1999 / 2000 : ℝ) := by 
    have h5 : ∀ (n : ℕ), ∑ i in Finset.range n, (1 + 1 / ((i + 1 : ℝ) * (i + 2)) ) = (↑n : ℝ) + (1 - 1 / (↑n + (1 : ℝ))) := by 
      intro n 
      induction n with 
      | zero => 
        norm_num 
      | succ n ih => 
        rw [Finset.sum_range_succ, ih]
        field_simp at *
        ring_nf
    specialize h5 1999 
    rw [h5]
    all_goals norm_num 
  rw [h4]
  rw [Int.floor_eq_iff]
  all_goals norm_num