import Mathlib

theorem algebra_94846 (a b c : ℕ) (ha : 0 < a ∧ a < 10) (hb : 0 < b ∧ b < 10) (hc : 0 < c ∧ c < 10)
    (h : b + c = 10) : (10 * a + b) * (10 * a + c) = 100 * a * (a + 1) + b * c := by
  have h1 : c + b = 10 := by 
    linarith
  have eq1 : (10 * a + b) * (10 * a + c) = 100 * a^2 + 10 * a * (b + c) + b * c := by
    ring_nf
    <;> omega
  have eq2 : 100 * a * (a + 1) + b * c = 100 * a^2 + 100 * a + b * c := by
    ring_nf
    <;> omega
  rw [eq1, eq2]
  have h4 : 10 * a * (b + c) = 100 * a := by 
    rw [h]
    all_goals 
      omega
  omega