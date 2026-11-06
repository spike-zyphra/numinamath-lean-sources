import Mathlib

theorem algebra_161242 {P : Polynomial ℝ} (hP : P.degree ≤ 2012)
    (hP1 : ∀ n : ℕ, n ∈ Finset.Icc 1 2012 → P.eval (n : ℝ) = 2 ^ n) :
    P.eval 0 ^ 2 + P.eval 2013 ^ 2 ≥ 1 - 2 ^ 2012 := by
  have h1 := hP1 1 (by norm_num)
  have h2 : P.eval 0 ^ 2 + P.eval 2013 ^ 2 ≥ 0 := by
    positivity
  have h3 : (1 - (2 : ℝ) ^ 2012) ≤ 0 := by
    norm_num
  linarith