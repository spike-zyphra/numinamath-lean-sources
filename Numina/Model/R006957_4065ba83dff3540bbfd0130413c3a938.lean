import Mathlib

theorem number_theory_121464 : ¬∃ n : ℕ, 0 < n ∧ n < 2310 ∧ 2310 ∣ n * (2310 - n) := by 
  rintro ⟨n, hn1, hn2, hdiv⟩
  interval_cases n <;> omega