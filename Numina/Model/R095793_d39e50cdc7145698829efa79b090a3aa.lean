import Mathlib

theorem number_theory_172038 {a b : ℤ} (h : ¬∃ d, d ≠ 0 ∧ d ∣ a - b ∧ d ∣ a + b) :
    ¬∃ d, d ≠ 0 ∧ d ∣ a ∧ d ∣ b := by
  rintro ⟨d, hdne0, hda, hdb⟩
  have h2 : d ∣ a - b := by
    have h3 : d ∣ a := hda
    have h4 : d ∣ b := hdb
    apply Int.dvd_sub
    exact h3
    exact h4
  have h3 : d ∣ a + b := by
    have h4 : d ∣ a := hda
    have h5 : d ∣ b := hdb
    apply Int.dvd_add
    exact h4
    exact h5
  have h_contra : ∃ d, d ≠ 0 ∧ d ∣ a - b ∧ d ∣ a + b := ⟨d, hdne0, h2, h3⟩
  exact h h_contra