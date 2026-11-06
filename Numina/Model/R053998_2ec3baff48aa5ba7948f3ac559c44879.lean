import Mathlib

open Real

theorem algebra_1817 {f : ℝ → ℝ} (hf : f = fun x => (1/3)*x^3 - (1/2)*x^2 + 3*x + 1/12) :
    ∑ i ∈ Finset.range 2013, f ((i + 1)/2014) = 6039/2 := by 
  rw [hf]
  norm_num [Finset.sum_range_succ]
  <;> ring_nf <;> norm_num