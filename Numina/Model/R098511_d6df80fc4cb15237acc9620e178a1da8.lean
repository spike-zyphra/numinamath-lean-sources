import Mathlib

theorem algebra_112781 (a b d : ℕ) (ha : a * 3 = b * 4) (hd : d * 6 = a * 7) (h : a + b + d = 70) :
    a = 24 ∧ b = 18 ∧ d = 28 := by 
  have ha1 : a = 24 := by
    try omega
  have hb1 : b = 18 := by
    rw [ha1] at ha
    try omega
  have hd1 : d = 28 := by
    rw [ha1] at hd
    try omega
  exact ⟨ha1, hb1, hd1⟩