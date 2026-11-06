import Mathlib

theorem number_theory_235753 {m n : ℕ} (hm : m < n) (hn : n < 2 * m) (hmn : m * n = 2013) :
    m = 33 ∧ n = 61 := by
  have h1 : m ≤ 2013 := by
    by_contra h
    push_neg at h
    have h2 : m * n > 2013 := by
      nlinarith [h, show n ≥ 1 by nlinarith]
    nlinarith
  have h2 : n ≤ 2013 := by
    by_contra h
    push_neg at h
    have h3 : m * n > 2013 := by
      nlinarith [h, show m ≥ 1 by nlinarith]
    nlinarith
  interval_cases m <;> omega