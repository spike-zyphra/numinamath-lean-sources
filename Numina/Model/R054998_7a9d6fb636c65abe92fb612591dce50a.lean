import Mathlib

theorem number_theory_253767 (x : ℕ) (hx : ∀ y : ℕ, x ∣ 7^y + 12 * y - 1) :
    x ≤ 18 := by
  have h1 := hx 1
  norm_num at h1
  have h2 : x ∣ 18 := h1
  have h3 : x ≤ 18 := by 
    exact Nat.le_of_dvd (by norm_num) h2
  exact h3