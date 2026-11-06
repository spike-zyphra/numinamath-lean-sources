import Mathlib

theorem number_theory_275700 (a b : ℤ) :
    (Even a ∧ Even b ∨ Odd a ∧ Odd b) → ∃ x y, (x^2 + y^2) = (a^2 + b^2) / 2 := by
  intro h
  rcases h with (⟨ha, hb⟩ | ⟨ha, hb⟩)
  · -- both even
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    use m + n, m - n
    have h1 : a = 2 * m := by
      linarith
    have h2 : b = 2 * n := by
      linarith
    have eq1 : a ^ 2 + b ^ 2 = 4 * (m ^ 2 + n ^ 2) := by
      rw [h1, h2]
      ring_nf
    have eq2 : (a ^ 2 + b ^ 2) / 2 = 2 * (m ^ 2 + n ^ 2) := by
      rw [eq1]
      omega
    have eq3 : (m + n) ^ 2 + (m - n) ^ 2 = 2 * (m ^ 2 + n ^ 2) := by
      ring
    linarith [eq2, eq3]
  · -- both odd
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    use m + n + 1, m - n
    have h1 : a = 2 * m + 1 := by
      linarith
    have h2 : b = 2 * n + 1 := by
      linarith
    have eq1 : a ^ 2 + b ^ 2 = 4 * (m ^ 2 + n ^ 2 + m + n) + 2 := by
      rw [h1, h2]
      ring_nf
    have eq2 : (a ^ 2 + b ^ 2) / 2 = 2 * (m ^ 2 + n ^ 2 + m + n) + 1 := by
      rw [eq1]
      omega
    have eq3 : (m + n + 1) ^ 2 + (m - n) ^ 2 = 2 * (m ^ 2 + n ^ 2 + m + n) + 1 := by
      ring
    linarith [eq2, eq3]
  all_goals omega