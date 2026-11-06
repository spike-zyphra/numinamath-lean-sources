import Mathlib

theorem inequalities_67338 (a : ℕ → ℝ) (ha : a 1 = 1)
    (h : ∀ n > 1, ∑ i ∈ Finset.range n, (n - i) * a (n - i) < 0 ∧
      ∑ i ∈ Finset.range n, (n - i)^2 * a (n - i) > 0) :
    ∑ i ∈ Finset.range 2013, (2013 - i)^3 * a (2013 - i) < 12345 := by

  -- Apply the hypothesis to n = 2, 3, 4, ... to get constraints
  have h2 := h 2 (by norm_num)
  norm_num [Finset.sum_range_succ] at h2
  all_goals
    try { 
      have h3 := h 3 (by norm_num)
      norm_num [Finset.sum_range_succ] at h3
      all_goals
        try { 
          have h4 := h 4 (by norm_num)
          norm_num [Finset.sum_range_succ] at h4
          all_goals
            try { linarith [ha] }
        }
    }