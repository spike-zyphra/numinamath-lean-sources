import Mathlib

theorem algebra_6392 {a b c : ℝ} (ha : 90 * a + 120 * b + 180 * c = 15)
    (hb : 70 * a + 100 * b + 120 * c = 11) (hc : 50 * a + 110 * b + 150 * c = 12.1) :
    a = 3 / 100 ∧ b = 7 / 200 ∧ c = 9 / 200 := by
  ring_nf at hc
  have ha1 : a = 3 / 100 := by 
    linarith
  have hb1 : b = 7 / 200 := by 
    linarith
  have hc1 : c = 9 / 200 := by 
    linarith
  exact ⟨ha1, hb1, hc1⟩