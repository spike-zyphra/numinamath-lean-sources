import Mathlib

theorem algebra_317988 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n) (h : a 2 + a 4 + a 6 + a 8 + a 10 = 80) :
    a 7 - (1 / 2) * a 8 = 8 := by 
  rcases ha with ⟨d, hd⟩
  have h2 : a 2 = a 0 + d * 2 := hd 2
  have h4 : a 4 = a 0 + d * 4 := hd 4
  have h6 : a 6 = a 0 + d * 6 := hd 6
  have h8 : a 8 = a 0 + d * 8 := hd 8
  have h10 : a 10 = a 0 + d * 10 := hd 10
  have h7 : a 7 = a 0 + d * 7 := hd 7
  rw [h2, h4, h6, h8, h10] at h
  rw [h7, h8]
  linarith