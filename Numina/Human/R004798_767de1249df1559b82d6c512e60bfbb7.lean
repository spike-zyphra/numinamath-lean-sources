import Mathlib

theorem number_theory_327585 (a b : ℕ) (ha : 0 < a ∧ a < 10) (hb : b < 10) (ha' : a ≠ 0)
    (h : 72 ∣ Nat.ofDigits 10 [b, 9, 7, 6, a]) :
    a = 3 ∧ b = 2 := by 
  simp [Nat.ofDigits] at h
  have h1 : a = 3 := by 
    omega
  have h2 : b = 2 := by 
    omega
  exact ⟨h1, h2⟩