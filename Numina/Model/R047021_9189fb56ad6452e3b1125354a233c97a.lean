import Mathlib

theorem algebra_157165 {f : ℝ → ℝ} (hf : ∀ x y, 1 < x → x < y → f (1 / x) - f (1 / y) = f ((x - y) / (1 - x * y))) :
    ∑ i ∈ Finset.range 8, f (1 / ((i + 1)^2 + 5*(i + 1) + 5)) = f (1 / 4) := by

  have h1 := hf 3 4 (by norm_num) (by norm_num)
  have h2 := hf 4 5 (by norm_num) (by norm_num)
  have h3 := hf 5 6 (by norm_num) (by norm_num)
  have h4 := hf 6 7 (by norm_num) (by norm_num)
  have h5 := hf 7 8 (by norm_num) (by norm_num)
  have h6 := hf 8 9 (by norm_num) (by norm_num)
  have h7 := hf 9 10 (by norm_num) (by norm_num)
  have h8 := hf 10 11 (by norm_num) (by norm_num)

  norm_num [Finset.sum_range_succ] at *
  linarith