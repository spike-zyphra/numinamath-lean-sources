import Mathlib

theorem number_theory_253307 {b g : ℕ} (hb : b ≠ 0) (hg : g ≠ 0)
    (hbg : b * 7 = g * 3) (h : b + g < 40 ∧ b + g > 30) :
    False := by 
  have h1 : b + g < 40 := h.1
  have h2 : b + g > 30 := h.2
  have h3 : b * 7 = g * 3 := hbg
  have h4 : g % 7 = 0 := by
    omega
  have h5 : ∃ k, g = 7 * k := by
    have : g % 7 = 0 := h4
    refine' ⟨g / 7, by omega⟩
  rcases h5 with ⟨k, h6⟩
  have h7 : b = 3 * k := by
    nlinarith
  have h8 : b + g = 10 * k := by
    omega
  have h9 : k > 3 := by
    omega
  have h10 : k < 4 := by
    omega
  omega