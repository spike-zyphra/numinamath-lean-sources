import Mathlib

theorem inequalities_215319 (x y : ℝ) (hx : 1 < x ∧ x < 3) (hy : 5 < y ∧ y < 7) :
    x / y ∈ Set.Ioo (1 / 7) (3 / 5) := by
  have h1 : 1 < x := hx.1
  have h2 : x < 3 := hx.2
  have h3 : 5 < y := hy.1
  have h4 : y < 7 := hy.2
  have h5 : 0 < y := by linarith
  -- To show 1/7 < x/y
  have h6 : 1 / 7 < x / y := by
    have h7 : 1 < x := h1
    have h8 : y < 7 := h4
    have h9 : 5 < y := h3
    apply (lt_div_iff' (by linarith)).mpr
    nlinarith
  -- To show x/y < 3/5
  have h7 : x / y < 3 / 5 := by
    have h9 : x < 3 := h2
    have h10 : 5 < y := h3
    have h11 : 5 * x < 3 * y := by
      nlinarith
    apply (div_lt_iff' (by linarith)).mpr
    linarith
  exact ⟨h6, h7⟩