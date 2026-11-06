import Mathlib

/- Yan is somewhere between his home and the stadium. To get to the stadium he can walk directly to the stadium, or else he can walk home and then ride his bicycle to the stadium. He rides 7 times as fast as he walks, and both choices require the same amount of time. What is the ratio of Yan's distance from his home to his distance from the stadium?
(A) 2/3
(B) 3/4
(C) 4/5
(D) 5/6
(E) 7/8 -/

theorem algebra_96613 (a b ws bs : ℝ) (ha : a > 0) (hb: b > 0) (h₀ : ws > 0) (h₁ : bs > 0)
(h₂ : a / ws = (a + b) / bs + b / ws) (h₃ : bs = 7 * ws) : b / a = 3 / 4 := by
  -- use bs = 7*ws to eliminate bs from h2
  rw [h₃] at h₂
  -- cancel out all ws
  have h₄ : a = (a + b) / 7 + b := calc
    a = (a / ws) * ws := by field_simp
    _ = ((a+b)/(7*ws) + b/ws) * ws := by rw [h₂]
    _ = (a+b)/(7*ws) * ws + b/ws * ws := by linarith
    _ = (a+b)/(7*ws) * ws + b := by field_simp
    _ = (a+b)/7 /ws * ws + b := by field_simp
    _ = (((a+b)/7) /ws * ws) + b := by field_simp
    _ = (a+b)/7 + b := by
      field_simp
      linarith
  -- simplify eqn more to get 6a = 8b
  have h₅ : a * 6 = b * 8 := calc
    a * 6 = a * 7 - a := by linarith
    _ = ((a + b)/7 + b) * 7 - a := by  rw [← h₄]
    _ = (a+b)/7*7 + b*7 - a := by field_simp
    _ = (a+b) + b*7 - a := by field_simp
    _ = b * 8 := by linarith
  -- divide by 8a to get b/a = 3/4
  have h₆ : (a * 6) / (a * 8) = (b * 8) / (a * 8) := by
    field_simp
    exact h₅
  calc
  b / a = (b * 8) / (a * 8) := by ring
  _ = (a * 6) / (a * 8) := by rw [h₆]
  _ = 3 / 4 := by
    ring_nf
    field_simp