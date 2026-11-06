import Mathlib

/- Example 1 A positive integer, when added to 100, becomes a perfect square. If 168 is added to it, it becomes another perfect square. Find this number.

-/
theorem number_theory_8046 {x : ℕ} (hx : ∃ n, n ^ 2 = x + 100) (hx' : ∃ m, m ^ 2 = x + 168) :
    x = 156 := by
  rcases hx with ⟨n, hn⟩
  rcases hx' with ⟨m, hm⟩
  -- Compare the two given conditions to get m² - n² = 68.
  have h₀ : m ^ 2 - n ^ 2 = 68 := by
    omega
  have h₁ : m > n := by
    nlinarith
  -- We show that m, n ≤ 34 and search for all cases to show that (m, n) = (18, 16).
  have h₂ : m ≤ 34 := by
    nlinarith
  have h₃ : n ≤ 34 := by
    nlinarith
  have h₄ : m = 18 ∧ n = 16 := by
    interval_cases m
    <;> interval_cases n
    <;> omega
  -- Conclude that x = 156.
  simp_all