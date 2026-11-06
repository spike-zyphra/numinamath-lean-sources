import Mathlib

theorem number_theory_273891 {n : ℕ} (hn : n % 19 = 17 ∧ n % 99 = 2) :
    n / 19 + n / 99 = 1999 ↔ n = 31880 := by
  rcases hn with ⟨ha, hb⟩
  constructor
  · -- Assume n / 19 + n / 99 = 1999, prove n = 31880
    intro h
    omega
  · -- Assume n = 31880, prove n / 19 + n / 99 = 1999
    intro h
    rw [h]
    all_goals omega