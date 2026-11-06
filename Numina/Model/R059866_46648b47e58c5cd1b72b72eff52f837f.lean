import Mathlib

theorem number_theory_294359 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a^2 + b^2 ∈ Finset.Icc 97 108) (h1 : a^2 > b^2) (h2 : 2 ≤ a^2) (h3 : 2 ≤ b^2)
    (h4 : Odd (a^2 + b^2)) :
    a^2 = 81 ∧ b^2 = 16 := by
  rw [Finset.mem_Icc] at h
  rcases h with ⟨h5, h6⟩
  have h7 : a ≤ 10 := by nlinarith [h5, h6, show a^2 ≥ 2 by nlinarith, show b^2 ≥ 2 by nlinarith]
  have h8 : b ≤ 10 := by nlinarith [h5, h6, show a^2 ≥ 2 by nlinarith, show b^2 ≥ 2 by nlinarith]
  interval_cases a <;> interval_cases b <;> norm_num [Nat.odd_iff] at *
    <;> omega