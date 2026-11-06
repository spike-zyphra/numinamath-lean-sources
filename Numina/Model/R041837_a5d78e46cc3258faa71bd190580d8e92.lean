import Mathlib

theorem number_theory_23028 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h : 66 ∣ (405 + 10 * a) ∧ 66 ∣ (100 * b + 32)) : a + b = 10 := by
        rcases h with ⟨h1, h2⟩
        -- Let's let Lean's omega tactic solve this arithmetic problem
        omega