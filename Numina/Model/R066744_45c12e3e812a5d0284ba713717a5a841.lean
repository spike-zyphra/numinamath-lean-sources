import Mathlib

theorem number_theory_165995 (a h l p : ℕ) (ha : a = 2 * p) (hl : Nat.Prime l)
    (hh : Nat.Prime h) (hhl : h > 10 * l) (h1 : a + h = 80) (h2 : l + p = 80) :
    a = 32 ∧ h = 16 ∧ l = 3 ∧ p = 59 := by
  rw [ha] at h1
  have h6 : 2 * p + h = 80 := h1
  omega