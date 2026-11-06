import Mathlib

theorem algebra_110673 (d t : ℕ) (ht : t > 0) (h : d / t = t) (h' : d / 2 + 1 = 11) :
    d = 16 := by
  have h1 : d / 2 = 10 := by
    omega -- compute h1 from h'
  have h2 : d = 20 ∨ d = 21 := by
    have h3 : d / 2 = 10 := h1
    omega -- compute possible d from h3
  rcases h2 with (h4 | h4)
  · -- assume d = 20
    rw [h4] at h
    have h3 : t ≤ 20 := by
      by_contra h4
      push_neg at h4
      have h5 : 20 / t = 0 := by
        rw [Nat.div_eq_zero_iff]
        omega
      rw [h5] at h
      all_goals
        omega
    interval_cases t <;> omega -- automatically invalid as Lean will compute
  · -- assume d = 21
    rw [h4] at h
    have h3 : t ≤ 21 := by
      by_contra h4
      push_neg at h4
      have h5 : 21 / t = 0 := by
        rw [Nat.div_eq_zero_iff]
        omega
      rw [h5] at h
      all_goals
        omega
    interval_cases t <;> omega -- automatically invalid