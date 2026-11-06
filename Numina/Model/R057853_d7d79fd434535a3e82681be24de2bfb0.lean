import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_218853 {f : ℝ → ℝ} (hf : f = λ z => sqrt (1.44 + 0.8 * (z + 0.3)^2)) :
    IsLeast (range f) (f (-0.3)) := by
  have h1 : f (-0.3) = Real.sqrt (1.44 + 0.8 * (-0.3 + 0.3)^2) := by
    rw [hf]
  have h2 : f (-0.3) = Real.sqrt 1.44 := by
    rw [h1]
    norm_num
  constructor
  · -- Show $f(-0.3)$ is in $range \ f$
    simpa using by norm_num [h2]
  · -- Show $f(-0.3)$ is minimum of $range \ f$
    intro y hy
    -- For all y ∈ range f, f(-0.3) ≤ y
    rcases hy with ⟨z, hz⟩
    have h3 : f z = Real.sqrt (1.44 + 0.8 * (z + 0.3)^2) := by 
      rw [hf]
    have h4 : f z ≥ f (-0.3) := by 
      rw [h3, h2]
      have h5 : Real.sqrt (1.44 + 0.8 * (z + 0.3)^2) ≥ Real.sqrt 1.44 := by 
        apply Real.sqrt_le_sqrt
        have h6 : (z + 0.3)^2 ≥ 0 := sq_nonneg (z + 0.3)
        have h7 : 0.8 * (z + 0.3)^2 ≥ 0 := mul_nonneg (by norm_num) h6
        linarith
      linarith
    linarith [hz, h4]