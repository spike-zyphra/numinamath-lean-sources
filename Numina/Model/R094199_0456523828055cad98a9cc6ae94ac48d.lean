import Mathlib

theorem number_theory_157213 (n : ℕ) (hn : Odd n ∧ 3 ≤ n) :
    ∃ a b, a ≠ b ∧ n = 2 * a * b / (a + b) := by
  rcases hn with ⟨h_odd, hn3⟩
  rcases h_odd with ⟨k, hk⟩
  use k + 1
  use (2 * k + 1) * (k + 1)
  constructor
  · -- Show that a ≠ b
    by_contra h
    have h2 : k + 1 = (2 * k + 1) * (k + 1) := by
      omega
    have h3 : k ≥ 1 := by
      omega
    have h4 : (2 * k + 1) * (k + 1) > k + 1 := by
      nlinarith
    linarith
  · -- Show that n = 2 * a * b / (a + b)
    have h4 : 2 * (k + 1) * ((2 * k + 1) * (k + 1)) = (2 * k + 1) * (2 * (k + 1)^2) := by
      ring
    have h5 : (k + 1) + ((2 * k + 1) * (k + 1)) = 2 * (k + 1)^2 := by
      ring
    have h6 : 2 * (k + 1) * ((2 * k + 1) * (k + 1)) / ((k + 1) + ((2 * k + 1) * (k + 1))) = (2 * k + 1) := by
      rw [h4, h5]
      field_simp
      <;> omega
    rw [show n = 2 * k + 1 by omega]
    simp [h6]
    all_goals omega