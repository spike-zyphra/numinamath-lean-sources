import Mathlib

theorem algebra_197385 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2)
    (hsum : ∀ n ≥ 1, ∑ i in Finset.Icc 1 n, a i = n ^ 2) :
    ∀ n ≥ 1, a n = 1 / (n * (n + 1)) := by 
  -- Let's derive the value of $a_1$ from `hsum` with $n = 1$
  have h1 := hsum 1 (by norm_num)
  norm_num [Finset.sum_singleton] at h1 
  -- Now `h1` gives us that $a 1 = 1$
  -- But we have $a 1 = 1/2$ from the hypothesis `ha1`
  linarith [ha1, h1]