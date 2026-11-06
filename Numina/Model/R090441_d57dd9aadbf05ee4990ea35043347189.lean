import Mathlib

theorem algebra_172312 {m : ℤ} (hm : |m| ≥ 2) (a : ℕ → ℤ)
    (ha : ¬(a 0 = 0 ∧ a 1 = 0)) (h : ∀ n, a (n + 2) = a (n + 1) - m * a n)
    (r s : ℕ) (hr : a r = a 0) (hs : a s = a 1) (hrrs : r > s ∧ s ≥ 3) :
    (Odd m ∨ 4 ∣ m) → r - s ≥ m ^ 2 ∧ ¬(Odd m ∨ 4 ∣ m) → r - s ≥ (1 / 2) * m ^ 2 := by 
  intro h1 h2
  have h_contra := h2.2 h1
  contradiction