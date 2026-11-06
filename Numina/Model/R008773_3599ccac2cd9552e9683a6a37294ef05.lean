import Mathlib

theorem algebra_21458 (n : ℕ) (h₀ : Even n) (h₁ : ∑ i ∈ Finset.range 3, (n + 2 * i)^2 = 12296) :
    (n * (n + 2) * (n + 4)) / 8 = 32736 := by
  simp [Finset.sum_range_succ] at h₁
  have h2 : n ≤ 75 := by nlinarith
  interval_cases n <;> omega
  <;> try { all_goals omega }