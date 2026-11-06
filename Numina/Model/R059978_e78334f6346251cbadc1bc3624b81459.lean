import Mathlib

theorem number_theory_19433 {n : ℕ} (hn : n % 5 = 3 ∧ n % 7 = 5) (h : n < 10 * 4) :
    n = 33 := by 
  rcases hn with ⟨h1, h2⟩
  have h3 : n < 40 := by norm_num at h; omega
  interval_cases n <;> omega