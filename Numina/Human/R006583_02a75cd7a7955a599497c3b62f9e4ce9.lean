import Mathlib

theorem number_theory_638785 (p a0 y0 : ℤ) (hp : Odd p ∧ Prime p)
    (hy0 : ¬p ∣ y0) (h : y0^2 ≡ a0 [ZMOD p]) :
    ∀ x, x^2 ≡ a0 [ZMOD p] ↔ (x ≡ y0 [ZMOD p] ∨ x ≡ -y0 [ZMOD p]) := by 
  intro x
  constructor 
  · 
    intro h1
    have pdvd : p ∣ x ^ 2 - y0 ^ 2 := by 
      refine Int.ModEq.dvd (id (Int.ModEq.symm ?_))
      calc 
        _ ≡ a0 [ZMOD p] := by 
          exact h1
        _ ≡ y0 ^ 2 [ZMOD p] := by 
          exact Int.ModEq.symm h
    have aux : x ^ 2 - y0 ^ 2 = (x - y0 ) * (x + y0)  := by 
      ring
    rw [aux] at pdvd
    have pdvd_or : p ∣ x - y0 ∨ p ∣ x + y0 := by
      refine Prime.dvd_or_dvd ?_ pdvd
      exact hp.2
    obtain hdvd | hdvd := pdvd_or
    left
    apply Int.ModEq.symm 
    exact Int.modEq_iff_dvd.mpr hdvd
    right
    apply Int.ModEq.symm
    refine Int.modEq_iff_dvd.mpr ?_ 
    simp
    exact hdvd
  · intro h1
    obtain h1 | h1 := h1
    · calc 
        _ ≡ y0 ^ 2 [ZMOD p] := by 
          exact Int.ModEq.pow 2 h1
        _ ≡ a0 [ZMOD p] := by assumption
    · calc 
        _ ≡ (-y0) ^ 2 [ZMOD p] := by
          exact Int.ModEq.pow 2 h1
        _ ≡ a0 [ZMOD p] := by 
          simp
          exact h
  