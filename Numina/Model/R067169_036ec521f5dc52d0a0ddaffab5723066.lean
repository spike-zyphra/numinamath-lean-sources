import Mathlib

theorem number_theory_321224 (a : ℕ → ℕ) (ha : ∀ n, a n > 0)
    (h1 : a 1 = 2) (h2 : ∀ n, a (n + 1) = a n ^ 2 - a n + 1) :
    ∀ m n, m ≠ n → Nat.Coprime (a m) (a n) := by
  intro m n hmn
  have h3 := h2 0 
  rw [h1] at h3 
  have h4 : a 0 > 0 := ha 0
  have h6 : a 0 ^ 2 = a 0 + 1 := by
    omega
  have h7 : a 0 ≤ 2 := by 
    nlinarith [sq_pos_of_pos h4]
  have h8 : a 0 = 1 ∨ a 0 = 2 := by 
    interval_cases (a 0) <;> omega
  rcases h8 with (h | h)
  · -- Let's check a 0 = 1 leads to a contradiction
    rw [h] at h6
    all_goals omega
  · -- Let's check a 0 = 2 leads to a contradiction
    rw [h] at h6
    all_goals omega