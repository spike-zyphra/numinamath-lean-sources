import Mathlib

theorem number_theory_287307 (n : ℕ) (hn : n ≥ 3) (a : ℕ → ℤ)
    (h₀ : ∀ i, i + 2 < n → a i + a (i + 1) + a (i + 2) > 0)
    (h₁ : ∀ i, i + 4 < n → a i + a (i + 1) + a (i + 2) + a (i + 3) + a (i + 4) < 0) :
    n ≤ 6 := by
  by_contra h
  push_neg at h
  have h2 : n ≥ 7 := by
    omega
  -- We derive a contradiction for n >= 7
  have h3 : a 0 + a 1 + a 2 > 0 := by
    have h4 : 0 + 2 < n := by
      omega
    specialize h₀ 0 h4
    simpa using h₀
  -- Apply h₀ for i = 1
  have h4 : a 1 + a 2 + a 3 > 0 := by
    have h5 : 1 + 2 < n := by
      omega
    specialize h₀ 1 h5
    simpa using h₀
  -- Apply h₀ for i = 2
  have h5 : a 2 + a 3 + a 4 > 0 := by
    have h6 : 2 + 2 < n := by
      omega
    specialize h₀ 2 h6
    simpa using h₀
  -- Apply h₀ for i = 3
  have h6 : a 3 + a 4 + a 5 > 0 := by
    have h7 : 3 + 2 < n := by
      omega
    specialize h₀ 3 h7
    simpa using h₀
  -- Apply h₀ for i = 4
  have h7 : a 4 + a 5 + a 6 > 0 := by
    have h8 : 4 + 2 < n := by
      omega
    specialize h₀ 4 h8
    simpa using h₀
  -- Apply h₁ for i = 0
  have h8 : a 0 + a 1 + a 2 + a 3 + a 4 < 0 := by
    have h9 : 0 + 4 < n := by
      omega
    specialize h₁ 0 h9
    simpa using h₁
  -- Apply h₁ for i = 1
  have h9 : a 1 + a 2 + a 3 + a 4 + a 5 < 0 := by
    have h10 : 1 + 4 < n := by
      omega
    specialize h₁ 1 h10
    simpa using h₁
  -- Apply h₁ for i = 2
  have h10 : a 2 + a 3 + a 4 + a 5 + a 6 < 0 := by
    have h11 : 2 + 4 < n := by
      omega
    specialize h₁ 2 h11
    simpa using h₁
  omega