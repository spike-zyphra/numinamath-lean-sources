import Mathlib

theorem number_theory_97831 {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hb : b < 2009) (h : ∃ k : ℕ, b = a * k ∧ 2009 = b * k) :
    a = 41 := by
  rcases h with ⟨k, h1, h2⟩
  have h3 : a * k ^ 2 = 2009 := by
    calc
      a * k ^ 2 = a * (k * k) := by ring
      _ = (a * k) * k := by ring
      _ = b * k := by rw [show a * k = b by linarith [h1]]
      _ = 2009 := by linarith [h2]
  have h5 : k ≤ 44 := by
    by_contra h6
    push_neg at h6
    have h6' : k ^ 2 ≥ 2025 := by
      have : k ≥ 45 := by omega
      nlinarith [this]
    have h7 : a * k ^ 2 = 2009 := by
      nlinarith [h3]
    nlinarith [show a ≥ 1 by nlinarith [h1, ha]]
  interval_cases k <;> omega