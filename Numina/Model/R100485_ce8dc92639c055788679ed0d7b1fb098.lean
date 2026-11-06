import Mathlib

theorem number_theory_116681 (x : ℕ) (hx : x > 0) (h : ∀ y > 0, x ∣ 7^y + 12 * y - 1) :
    x ≤ 18 := by 
  have h1 := h 1 (by norm_num)
  have h18 : x ∣ 18 := by 
    exact h1
  have h6 : x ≤ 18 := by 
    apply Nat.le_of_dvd (by norm_num) h18
  linarith