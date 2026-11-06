import Mathlib

open Real

theorem algebra_320356 : round (∑ i ∈ Finset.range 1997, sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2)) = 1998 := by

  have h1 : ∀ i : ℕ, sqrt (1 + 1 / (i + 1) ^ 2 + 1 / (i + 2) ^ 2) = 1 + 1 / ((i + 1) * (i + 2)) := by
    intro i
    have h2 : (1 + 1 / (i + 1 : ℝ) ^ 2 + 1 / (i + 2 : ℝ) ^ 2) = (1 + 1 / ((i + 1 : ℝ) * (i + 2 : ℝ))) ^ 2 := by
      field_simp
      <;> ring_nf <;> field_simp
      <;> ring
    rw [h2]
    have h3 : (1 + 1 / ((i + 1 : ℝ) * (i + 2 : ℝ)) : ℝ) ≥ 0 := by
      positivity
    rw [Real.sqrt_sq (h3)]

  have h2 : ∑ i in Finset.range 1997, sqrt (1 + 1 / (i + 1) ^ 2 + 1 / (i + 2) ^ 2) = 
          ∑ i in Finset.range 1997, (1 + 1 / ((i + 1 : ℝ) * (i + 2 : ℝ))) := by 
    apply Finset.sum_congr 
    . rfl 
    intro i hi 
    specialize h1 i 
    simpa using h1

  rw [h2]
  have h3 : ∑ i in Finset.range 1997, (1 + 1 / ((i + 1 : ℝ) * (i + 2 : ℝ))) = (1998 - 1 / 1998 : ℝ) := by 
    have h4 : ∀ n : ℕ, ∑ i in Finset.range n, (1 + 1 / ((i + 1 : ℝ) * (i + 2 : ℝ))) = (↑n + 1 - 1 / (↑n + 1 : ℝ)) := by
      intro n
      induction n with
      | zero =>
        simp
        <;> norm_num
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp at *
        ring_nf
        <;> field_simp at *
        <;> ring
    specialize h4 1997
    norm_num at h4 ⊢ 
    <;> linarith
  rw [h3]
  norm_num [round_eq]
  all_goals norm_num