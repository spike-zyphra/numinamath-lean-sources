import Mathlib

open Real
theorem algebra_608684
(k: ℝ)
(hk : k ≠ 0)
(f : ℝ → ℝ)
(hf : f = fun x => x + 1 / x)
(hsymm : ∀ x1, ∃ x2, x2 ≠ 0 ∧ x2 ≠ x1 ∧  x1 + x2 ≠ 0 ∧ (f x2 - f x1) / (x2 - x1) = -1 / k ∧ (f x1+f x2) / 2 = k * (x1 + x2) / 2):
k = 1-sqrt 2 ∨ k = 1+sqrt 2:= by

  have h1 := hsymm 0
  rcases h1 with ⟨x2, hx21, hx22, hx23, h1, h2⟩

  have h3 : x2 ≠ 0 := hx21

  have h4 : f 0 = 0 := by
    rw [hf]
    norm_num

  have h5 : f x2 = x2 + 1 / x2 := by
    rw [hf]

  have eq1 : (f 0 + f x2) / 2 = k * (0 + x2) / 2 := by
    simpa using h2

  rw [h4, h5] at eq1

  have eq2 : x2 + 1 / x2 = k * x2 := by
    have h3' : x2 ≠ 0 := h3
    field_simp at eq1 ⊢
    nlinarith [sq_pos_of_ne_zero (show x2 ≠ 0 by exact h3)]

  have eq3 : (f x2 - f 0) / (x2 - (0 : ℝ)) = -1 / k := by
    simpa using h1

  rw [h4, h5] at eq3

  have eq4 : (x2 + 1 / x2) / x2 = -1 / k := by
    have h3' : x2 ≠ 0 := h3
    field_simp at eq3 ⊢
    nlinarith

  have eq5 : (x2 + 1 / x2) / x2 = (x2 ^ 2 + 1) / (x2 ^ 2) := by
    have h3' : x2 ≠ 0 := h3
    field_simp
    <;> ring

  rw [eq5] at eq4

  have eq6 : x2 ^ 2 + 1 = k * x2 ^ 2 := by
    have h3' : x2 ≠ 0 := h3
    field_simp at eq2 ⊢
    nlinarith

  have eq13 : k ^ 2 = -1 := by
    have h9 : x2 ≠ 0 := h3
    have h9' : x2 ^ 2 > 0 := by
      exact sq_pos_of_ne_zero h9
    field_simp at eq4 eq6 ⊢
    nlinarith [sq_pos_of_ne_zero hk, sq_pos_of_ne_zero (show x2 ≠ 0 by exact h3)]

  have h9 : k ^ 2 ≥ 0 := by
    exact sq_nonneg k

  nlinarith [Real.sqrt_nonneg 2]