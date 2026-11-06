import Mathlib
theorem algebra_611090 (a b c : ℂ) (h : ∀ x : ℝ, x ^ 3 + x ^ 2 - 333 * x - 1001 = (x - a) * (x - b) * (x - c)) : a ^ 3 + b ^ 3 + c ^ 3 = 2003:= by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  simp [Complex.ext_iff, pow_two, pow_three] at eq1 eq2 eq3 eq4
  have h1 : a + b + c = -1 := by
    norm_num [Complex.ext_iff] at eq1 eq2 eq3 eq4 ⊢
    ring_nf at eq1 eq2 eq3 eq4 ⊢
    constructor
    · ring_nf at eq1 eq2 eq3 eq4 ⊢
      linarith 
    · ring_nf at eq1 eq2 eq3 eq4 ⊢
      linarith
  have h2 : a * b + a * c + b * c = -333 := by
    norm_num [Complex.ext_iff] at eq1 eq2 eq3 eq4 ⊢
    ring_nf at eq1 eq2 eq3 eq4 ⊢
    constructor
    · ring_nf at eq1 eq2 eq3 eq4 ⊢
      linarith 
    · ring_nf at eq1 eq2 eq3 eq4 ⊢
      linarith
  have h3 : a * b * c = 1001 := by
    norm_num [Complex.ext_iff] at eq1 eq2 eq3 eq4 ⊢
    ring_nf at eq1 eq2 eq3 eq4 ⊢
    constructor
    · ring_nf at eq1 eq2 eq3 eq4 ⊢
      linarith 
    · ring_nf at eq1 eq2 eq3 eq4 ⊢
      linarith
  have h4 : a ^ 3 + b ^ 3 + c ^ 3 = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + a * c + b * c) + 3 * (a * b * c) := by
    ring_nf
  rw [h4]
  rw [h1, h2, h3]
  norm_num [pow_three, Complex.ext_iff]