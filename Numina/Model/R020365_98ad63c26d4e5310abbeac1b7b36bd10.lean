import Mathlib

theorem number_theory_288690 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ q : ℚ, a * q = b ↔ ∃ c d : ℤ, 0 < c ∧ 0 < d ∧ a * c = b * d := by
  use (b : ℚ) / (a : ℚ)
  constructor
  · -- Assume a * q = b, prove ∃ c d : ℤ, 0 < c ∧ 0 < d ∧ a * c = b * d
    intro h
    have h31 : (↑a : ℚ) * (↑b / ↑a) = (↑b : ℚ) := by 
      field_simp
    have h53 : (↑a : ℤ) * (↑b : ℤ) = (↑b : ℤ) * (↑a : ℤ) := by
      ring
    refine' ⟨(b : ℤ), (a : ℤ), by omega, by omega, by simpa using h53⟩
  · -- Assume ∃ c d : ℤ, 0 < c ∧ 0 < d ∧ a * c = b * d, prove a * q = b
    intro h
    rcases h with ⟨c, d, hc, hd, h1⟩
    field_simp