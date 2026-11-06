import Mathlib

theorem number_theory_32831 {a r : ℕ} (hr : r > 0) (h : a * r^36 = b) (ha : 0 < a) (hb : 0 < b)
    (hrel : Nat.Coprime a b) :
    ∃ c, 0 < c ∧ a * r^18 = c^18 := by

  have h1 : Nat.Coprime a b := hrel
  rw [show b = a * r^36 by nlinarith] at h1

  -- `Nat.Coprime a (a * r ^ 36)` means that `Nat.gcd a (a * r ^ 36) = 1`.
  -- But gcd(a, a * r^36) = a, so it implies a = 1.
  have h2 : a = 1 := by
    have h3 : Nat.gcd a (a * r^36) = 1 := by 
      rw [Nat.coprime_iff_gcd_eq_one] at h1
      exact h1

    have h4 : Nat.gcd a (a * r^36) = a := by 
      simp [Nat.gcd_mul_right]
    
    rw [h4] at h3 
    linarith

  use r
  constructor
  · -- Show that r > 0
    linarith
  · -- Show that a * r^18 = r^18
    rw [show a = 1 by linarith [h2]]
    all_goals
      ring