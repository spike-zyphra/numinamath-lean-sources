import Mathlib

theorem number_theory_160065 (x y : ℕ) (h₀ : x * y = 1980) (h₁ : x ^ 2 = x + y) :
    x = 45 := by
  have h2 : x ≤ 44 := by
    by_contra h
    push_neg at h
    have h3 : x ≥ 45 := by omega
    have h4 : y ≤ 44 := by nlinarith [h₀, h3]
    nlinarith [h₁, h4, sq_nonneg (x - 45), sq_nonneg (y - 44)]
  interval_cases x <;> try { omega } <;> omega