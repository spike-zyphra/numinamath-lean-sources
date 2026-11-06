import Mathlib

theorem algebra_10484 (fy : ℝ → ℝ) (hfy : fy = fun (x : ℝ) => (1-x) / (2*x+3)):
    {-1/2} = {fy x | x ≠ -3/2}ᶜ := by
  ext y
  simp [hfy]
  constructor
  . rintro rfl x hx h
    field_simp [show 2 * x + 3 ≠ 0 by linarith +splitNe only [hx]] at h
    linarith only [h]
  . intro h
    contrapose! h
    set x := (1 - 3 * y) / (2 * y + 1) with hx
    use x
    field_simp [show 2 * y + 1 ≠ 0 by linarith +splitNe only [h]] at hx
    have hxne : x ≠ -3/2 := by
      intro hxeq
      rw [hxeq] at hx
      linarith only [hx]
    use hxne
    field_simp [show 2 * x + 3 ≠ 0 by linarith +splitNe only [hxne]]
    linarith only [hx]
