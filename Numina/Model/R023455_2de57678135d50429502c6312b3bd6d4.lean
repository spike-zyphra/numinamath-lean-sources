import Mathlib

theorem number_theory_139066 (n : ℕ) :
    ∃ m : ℕ, m^2 = n ∨ Irrational (Real.sqrt n) := by 
  by_cases h : IsSquare (n : ℕ)
  · -- If n is a perfect square, then we can find m such that m^2 = n.
    rcases h with ⟨m, hm⟩
    use m
    left
    have h1 : m ^ 2 = n := by
      nlinarith
    exact h1
  · -- If n is not a perfect square, then sqrt n is irrational.
    have h2 : ¬IsSquare (n : ℕ) := h
    use 0
    right
    have h3 : Irrational (Real.sqrt (n : ℝ)) := by
      rw [irrational_sqrt_natCast_iff]
      exact (show ¬IsSquare (n : ℕ) by exact h2)
    exact_mod_cast h3