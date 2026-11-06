import Mathlib

theorem number_theory_253998 (n : ℕ) (h : n = 12) :
    IsSquare (2^8 + 2^11 + 2^n) := by 
  rw [h]
  -- 2^12 = 4096 + 2048 + 256 = 6400
  -- 2^8 + 2^11 + 2^12 = 256 + 2048 + 4096 = 6400 = 80^2
  exact ⟨80, by norm_num⟩