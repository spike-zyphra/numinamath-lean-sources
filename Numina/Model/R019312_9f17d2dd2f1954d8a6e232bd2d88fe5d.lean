import Mathlib

theorem number_theory_1498
    (a b c d : ℤ)
    (h : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = 1993) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1994 := by
  have h1 : (a ^ 2 + b ^ 2) ∣ 1993 := by
    use (c ^ 2 + d ^ 2)
    all_goals linarith

  have h2 : (a ^ 2 + b ^ 2) = 1 ∨ (a ^ 2 + b ^ 2) = 1993 := by
    have h3 : (a ^ 2 + b ^ 2) ∣ 1993 := h1
    have h4 : (a ^ 2 + b ^ 2) ≥ 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    have h5 : (a ^ 2 + b ^ 2) ≤ 1993 := by
      apply Int.le_of_dvd (by norm_num) h3
    interval_cases h : (a ^ 2 + b ^ 2) <;> omega

  rcases h2 with h2 | h2
  · 
    have h3 : c ^ 2 + d ^ 2 = 1993 := by
      have h4 : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = 1993 := h
      rw [h2] at h4
      linarith
    linarith [h2, h3]
  · 
    have h3 : c ^ 2 + d ^ 2 = 1 := by
      have h4 : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = 1993 := h
      rw [h2] at h4
      linarith
    linarith [h2, h3]