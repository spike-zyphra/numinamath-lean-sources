import Mathlib
open Real

theorem algebra_4492 : ∑ i ∈ Finset.range 2016, (1 / (√(i + 1) + √(i + 2))) = √2017 - 1 := by

  have h1 : ∀ i : ℕ, 1 / (√(i + 1) + √(i + 2)) = √(i + 2) - √(i + 1) := by
    intro i
    have eq1 : (√(i + 1) + √(i + 2)) > 0 := by 
      have h1 : √(i + 1) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith [show (i : ℝ) + 1 > 0 by positivity]
      have h2 : √(i + 2) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith [show (i : ℝ) + 2 > 0 by positivity]
      linarith
    have eq2 : (√(i + 2) - √(i + 1)) * (√(i + 1) + √(i + 2)) = 1 := by
      nlinarith [Real.sqrt_nonneg (i + 1 : ℝ), Real.sqrt_nonneg (i + 2 : ℝ),
        sq (√(i + 1)), sq (√(i + 2)), 
        Real.sq_sqrt (show (i + 1 : ℝ) ≥ 0 by positivity), 
        Real.sq_sqrt (show (i + 2 : ℝ) ≥ 0 by positivity)]
    have h2 : (√(i + 2) - √(i + 1)) = 1 / (√(i + 1) + √(i + 2)) := by
      field_simp [eq1]
      <;> linarith 
    exact h2.symm

  rw [Finset.sum_congr rfl (fun i _ => h1 i)]

  have h2 : ∀ n : ℕ, (∑ i ∈ Finset.range n, (√(i + 2) - √(i + 1))) = √(n + 1) - 1 := by 
    intro n
    induction n with 
    | zero => 
      norm_num 
    | succ n ih => 
      rw [Finset.sum_range_succ, ih]
      field_simp [Real.sqrt_nonneg]
      <;> ring_nf

  have eq3 := h2 2016
  have eq4 : √((2016 : ℕ) + 1) = √(2017 : ℝ) := by
    norm_num
  rw [eq4] at eq3 
  linarith [eq3]