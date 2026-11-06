import Mathlib

theorem number_theory_240982 {a b c m n : ℤ} (ha : a = m^2 - n^2) (hb : b = 2 * m * n)
    (hc : c = m^2 + n^2) (h : a^2 + b^2 = c^2) (hm : m > 0) (hn : n > 0)
    (hmn : m = n + 1) :
    Odd c ∧ (Even a ∧ Odd b ∨ Odd a ∧ Even b) := by 
  have h1 : a = 2 * n + 1 := by
    rw [ha]
    have : m^2 - n^2 = (m - n) * (m + n) := by
      ring
    rw [this, hmn]
    ring_nf
    <;> nlinarith
  have h2 : b = 2 * (n^2 + n) := by
    rw [hb, hmn]
    ring_nf
    <;> nlinarith
  have h3 : c = 2 * (n^2 + n) + 1 := by
    rw [hc, hmn]
    ring_nf
    <;> nlinarith
  have h4 : Odd c := by
    rw [h3]
    exact ⟨n^2 + n, by ring⟩
  have h5 : Odd a := by
    rw [h1]
    exact ⟨n, by ring⟩
  have h6 : Even b := by
    rw [h2]
    exact ⟨n^2 + n, by ring⟩
  exact ⟨h4, Or.inr ⟨h5, h6⟩⟩