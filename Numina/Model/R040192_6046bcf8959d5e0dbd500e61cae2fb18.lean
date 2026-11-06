import Mathlib

theorem number_theory_290360 (a b : ℕ) (ha : a ∈ Finset.Icc 100 999) (hb : b ∈ Finset.Icc 100 999)
    (h : (1000 * a + b) = 7 * (a * b)) :
    a = 143 ∧ b = 143 := by
  rw [Finset.mem_Icc] at ha hb
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  have h1 : a ≥ 100 := ha1
  have h2 : a ≤ 999 := ha2
  have h3 : b ≥ 100 := hb1
  have h4 : b ≤ 999 := hb2
  interval_cases a <;> omega