import Mathlib

theorem number_theory_99475 (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a < 10 ∧ b < 10 ∧ c < 10) :
    3 ∣ (a * 100 + b * 10 + c) + (b * 100 + c * 10 + a) + (c * 100 + a * 10 + b) ∧
    ¬(28 ∣ (a * 100 + b * 10 + c) + (b * 100 + c * 10 + a) + (c * 100 + a * 10 + b)) := by
  rcases h with ⟨ha1, hb1, hc1⟩
  constructor
  · -- Show that A is divisible by 3
    have h1 : (a * 100 + b * 10 + c) + (b * 100 + c * 10 + a) + (c * 100 + a * 10 + b) = 111 * (a + b + c) := by 
      omega
    rw [h1]
    omega
  · -- Show that A is not divisible by 28
    intro h28
    have h1 : (a * 100 + b * 10 + c) + (b * 100 + c * 10 + a) + (c * 100 + a * 10 + b) = 111 * (a + b + c) := by 
      omega
    rw [h1] at h28
    have h2 : a < 10 := by linarith
    have h3 : b < 10 := by linarith
    have h4 : c < 10 := by linarith
    interval_cases a <;> interval_cases b <;> interval_cases c
    <;> omega