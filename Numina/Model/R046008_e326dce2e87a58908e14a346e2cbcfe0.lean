import Mathlib
open Mathlib

theorem number_theory_93943 : ¬∃ p : ℕ, p.Prime ∧ p < 10 ∧ p ∣ (2^607 - 1) := by
  rintro ⟨p, hp, hp10, hpdiv⟩
  interval_cases p <;> norm_num at hp hpdiv hp10 ⊢
  <;> omega