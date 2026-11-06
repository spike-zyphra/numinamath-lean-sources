import Mathlib

open Real

/-
Doug and Ryan are competing in the 2005 Wiffle Ball Home Run Derby.
In each round, each player takes a series of swings until they make an out. Doug has a 1/3 chance of hitting a home run per swing. Ryan has a 1/2 chance of hitting a home run per swing. We need to calculate the probability that Doug hits more home runs than Ryan.
-/
theorem combinatorics_611327 
    (p : ℝ) 
    (hp : p = ∑' n : ℕ, 
    ((1 : ℝ) / 3) ^ (n + 1) * ((1 : ℝ) / 2) ^ (n + 1)) :
    p = 1 / 5 := by

  -- Prove that the sum of ((1/3)^(n+1) * (1/2)^(n+1)) equals the sum of (1/6)^(n+1)
  have t₁ : ∑' n : ℕ, ((1 : ℝ) / 3) ^ (n + 1) * ((1 : ℝ) / 2) ^ (n + 1)=∑' n : ℕ , ((1 : ℝ) / 6) ^ (n + 1) := by

    -- First, show element-wise equality for each term in the series
    have h : ∀ n : ℕ , ((1 : ℝ) / 3) ^ (n + 1) * ((1 : ℝ) / 2) ^ (n + 1) = ((1 : ℝ) / 6) ^ (n + 1) := by
      intro n
      calc
        ((1 : ℝ) / 3) ^ (n + 1) * ((1 : ℝ) / 2) ^ (n + 1) = ((1 : ℝ) / 3 * ((1 : ℝ) / 2)) ^ (n + 1) := by
          rw [mul_pow]
        _ = ((1 : ℝ) / 6) ^ (n + 1) := by
          norm_num

    -- Then, use term-wise equality to prove equality of the infinite sums
    calc
      ∑' n : ℕ , ((1 : ℝ) / 3) ^ (n + 1) * ((1 : ℝ) / 2) ^ (n + 1) = ∑' n : ℕ , ((1 : ℝ) / 6) ^ (n + 1) := by
        apply tsum_congr
        intro n
        rw [h n]
      _ = ∑' n : ℕ , ((1 : ℝ) / 6) ^ (n + 1) := by rfl
  rw [hp, t₁]

  -- Prove that the sum of (1/6)^(n+1) equals 1/5
  have t₂: ∑' (n : ℕ) , ((1 : ℝ) / 6) ^ (n + 1) = 1 / 5 := by

    have h : ∑' (n : ℕ) , ((1 : ℝ) / 6) ^ (n + 1) = ∑' (n : ℕ) , ((1 : ℝ) / 6) * ((1 : ℝ) / 6) ^ n := by
      congr
      ext n
      ring_nf
    rw [h]

    -- Factor out the constant term using the linearity of infinite sums
    rw [tsum_mul_left]

    -- Apply the geometric series formula for |r| < 1: sum(r^n) = 1/(1-r)
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
    
  -- Simplify the goal using the equalities we've proven
  simp_all only [t₁,t₂]