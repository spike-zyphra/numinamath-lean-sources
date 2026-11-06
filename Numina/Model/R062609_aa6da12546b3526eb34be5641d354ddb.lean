import Mathlib

theorem number_theory_128435 (x y : ℤ) : 143 * x - 77 * y = 187 ↔ ∃ t, x = 4 + 7 * t ∧ y = 5 + 13 * t := by 
  constructor
  · -- Forward direction: if 143 * x - 77 * y = 187, then there exists t such that x = 4 + 7 * t and y = 5 + 13 * t
    intro h
    have eq1 : 143 * (x - 4) - 77 * (y - 5) = 0 := by
      linarith 
    have eq2 : 143 * (x - 4) = 77 * (y - 5) := by
      linarith 
    have h3 : (x - 4) % 7 = 0 := by
      omega 
    have h4 : (y - 5) % 13 = 0 := by
      omega 
    have hx : ∃ k, x - 4 = 7 * k := by
      refine ⟨(x - 4) / 7, by omega⟩
    rcases hx with ⟨k, hk⟩
    have hy : ∃ l, y - 5 = 13 * l := by
      refine ⟨(y - 5) / 13, by omega⟩
    rcases hy with ⟨l, hl⟩
    have eq3 : 143 * (7 * k) = 77 * (13 * l) := by 
      linarith [eq1, hk, hl]
    have eq4 : 143 * 7 * k = 77 * 13 * l := by
      linarith
    have eq5 : 1001 * k = 1001 * l := by
      linarith
    have eq6 : k = l := by
      linarith
    use k
    constructor
    · -- Show that x = 4 + 7 * k
      linarith [hk]
    · -- Show that y = 5 + 13 * l 
      have : l = k := by linarith [eq6]
      rw [this] at hl
      linarith
  · -- Reverse direction: if there exists t such that x = 4 + 7 * t and y = 5 + 13 * t, then 143 * x - 77 * y = 187
    rintro ⟨t, hx, hy⟩
    rw [hx, hy]
    linarith