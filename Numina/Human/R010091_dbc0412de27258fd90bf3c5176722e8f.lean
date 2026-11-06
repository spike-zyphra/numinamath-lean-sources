import Mathlib

/- What is the smallest positive integer with exactly 14 positive divisors? -/
theorem number_theory_15697 :
    IsLeast {n | 0 < n ∧ (n.divisors.card = 14)} 192 := by
  refine' ⟨by decide, fun n hn => _⟩
  refine' le_of_not_lt fun hn' => _
  interval_cases n <;> contradiction