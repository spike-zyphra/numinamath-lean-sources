import Mathlib

theorem number_theory_19042 {n : ℕ} (hn : n > 0) (h : Even n) (h' : Even (n + 2)) (h'' : n * (n + 2) = 288) :
    n + 2 = 18 := by
  have h1 : n ≤ 17 := by
    -- Assume n > 17, then n ≥ 18
    by_contra h2
    push_neg at h2
    have h3 : n ≥ 18 := by linarith
    -- Then n * (n + 2) ≥ 18 * 20 = 360
    have h4 : n * (n + 2) ≥ 18 * 20 := by
      have h5 : n + 2 ≥ 20 := by linarith
      nlinarith [h3, h5]
    -- But 18 * 20 = 360 > 288
    norm_num at h4 h''
    -- Contradiction since n * (n + 2) = 288 < 360
    all_goals linarith
  interval_cases n <;> omega