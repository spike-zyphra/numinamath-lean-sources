import Mathlib

theorem number_theory_14823 (b : ℕ) (hb : 6 < b) (h : Nat.ofDigits b [1, 6, 1] +
    Nat.ofDigits b  [4, 3, 1] = Nat.ofDigits b [5, 1, 3]) :
    b = 8 := by 
  simp [Nat.ofDigits, List.foldl] at h 
  nlinarith [h, hb]