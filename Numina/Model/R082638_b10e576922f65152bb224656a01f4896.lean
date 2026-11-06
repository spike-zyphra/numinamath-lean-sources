import Mathlib

theorem number_theory_133398 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) :
    IsSquare (400 * 10000 + n) ↔ n = 4001 ∨ n = 8004 := by

  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀, h₁⟩

  constructor
  · -- Assume that 400 * 10000 + n is a perfect square, prove n = 4001 ∨ n = 8004
    intro h
    rcases h with ⟨m, hm⟩

    have h4 : m ≤ 2002 := by
      nlinarith [show 400 * 10000 + n ≤ 4009999 by linarith, sq_nonneg m]

    have m2000 : m ≥ 2000 := by
      nlinarith [show 400 * 10000 + n ≥ 4001000 by linarith, sq_nonneg m]

    interval_cases m <;> omega

  · -- Assume n = 4001 ∨ n = 8004, prove that 400 * 10000 + n is a perfect square
    rintro (h | h)
    · -- Case n = 4001, so 400 * 10000 + 4001 = 2001^2
      rw [h]
      exact ⟨2001, by norm_num⟩

    · -- Case n = 8004, so 400 * 10000 + 8004 = 2002^2
      rw [h]
      exact ⟨2002, by norm_num⟩