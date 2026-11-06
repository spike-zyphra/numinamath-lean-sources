import Mathlib

theorem number_theory_184383 (a b c : ℕ) (ha : a < 10) (hb : b < 10) (hc : c < 10)
    (h1 : 5 ∣ 2016000 + 100 * a + 10 * b + c) (h2 : 7 ∣ 2016000 + 100 * a + 10 * b + c)
    (h3 : 13 ∣ 2016000 + 100 * a + 10 * b + c) :
    2016000 + 100 * a + 10 * b + c = 2016105 ∨ 2016000 + 100 * a + 10 * b + c = 2016560 := by 
  have h4 : c = 0 ∨ c = 5 := by 
    omega 
  cases h4 with
  | inl hc0 =>
    rw [hc0] at h1 h2 h3
    have h5 : a ≤ 9 := by linarith
    have h6 : b ≤ 9 := by linarith
    interval_cases a <;> interval_cases b <;> omega
  | inr hc5 =>
    rw [hc5] at h1 h2 h3
    have h5 : a ≤ 9 := by linarith
    have h6 : b ≤ 9 := by linarith
    interval_cases a <;> interval_cases b <;> omega