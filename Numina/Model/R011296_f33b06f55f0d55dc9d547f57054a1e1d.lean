import Mathlib

theorem number_theory_233966 (Ω : ℕ) (hx : Ω * Ω = 2 * 2 * 2 * 2 * 3 * 3) :
    Ω = 2 * 2 * 3 := by
  have h1 : Ω * Ω = 144 := by
    norm_num at hx ⊢
    exact hx
  have h2 : Ω ≤ 12 := by
    have h3 : Ω * Ω ≤ 12 * 12 := by 
      nlinarith [h1]
    nlinarith
  have h3 : Ω ≥ 12 := by
    by_contra h
    push_neg at h
    have h4 : Ω < 12 := by linarith
    interval_cases Ω <;> omega
  have h4 : Ω = 12 := by 
    linarith 
  calc 
    Ω = 12 := h4 
    _ = 2 * 2 * 3 := by norm_num