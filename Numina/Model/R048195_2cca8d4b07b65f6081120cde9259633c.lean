import Mathlib

theorem algebra_185222 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : y = x + 1 / x)
    (h : x ^ 4 + x ^ 3 - 4 * x ^ 2 + x + 1 = 0) :
    x ^ 2 * (y ^ 2 + y - 6) = 0 := by

  have eq1 : x ^ 2 + 1 / x ^ 2 = y ^ 2 - 2 := by
    have eq2 : y = x + 1 / x := hxy
    rw [eq2]
    field_simp [hx]
    <;> nlinarith (config := {splitNe := True})
  have eq3 : x ^ 4 + x ^ 3 - 4 * x ^ 2 + x + 1 = x ^ 2 * ( (x ^ 2 + 1 / x ^ 2 ) + (x + 1 / x) - 4 ) := by
    field_simp [hx]
    ring
  rw [eq3] at h
  have eq4 : x + 1 / x = y := by 
    linarith [hxy]
  rw [eq1] at h
  rw [eq4] at h
  ring_nf at h ⊢
  <;> try { nlinarith } <;> tauto