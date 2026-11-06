import Mathlib

/- Let the square number ${{y}^{2}}$ be the sum of the squares of 11 consecutive integers, then the minimum value of $y$ is ___          ___. -/
theorem number_theory_184 (y : ℕ) (h : ∃ n, y^2 = ∑ i ∈ Finset.range 11, (n + i)^2) :
    y ≥ 11 := by
  rcases h with ⟨n, hn⟩

  have h1 : y^2 = 11 * n^2 + 110 * n + 385 := by
    simp [Finset.sum_range_succ, add_sq] at hn ⊢
    ring_nf at hn ⊢
    nlinarith

  by_contra h2
  push_neg at h2

  have h3 : y < 11 := h2

  have h4 : y ≤ 10 := by linarith

  have h5 : y^2 < 121 := by
    nlinarith

  have h7 : y^2 = 11 * n^2 + 110 * n + 385 := h1

  -- Now, determine all possible bounds for n such that y^2 < 121
  have h8 : n ≤ 15 := by
    nlinarith [sq_nonneg (n + 5), h7, h4]

  have h9 : n ≤ 15 := by
    nlinarith [sq_nonneg (n + 5), h7, h4]

  -- exhaustive checking of small cases
  interval_cases y <;> try { 
    have h10 : n ≤ 15 := by
      nlinarith [sq_nonneg (n + 5), h7]
    interval_cases n <;> omega
  }
  <;> omega