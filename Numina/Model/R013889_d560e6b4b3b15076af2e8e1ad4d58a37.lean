import Mathlib

theorem algebra_4730
    (f : ℕ → ℕ)
    (h₀ : ∀ n, f (f n + 3) = n ^ 4 - 2 * n ^ 3 + 6 * n ^ 2 - 5 * n + 7)
    (h₁ : ∀ n, f (n + 1) + 2 * n = f n) :
    False := by
  have eq1 := h₀ 0
  have eq2 := h₁ 0
  have eq3 := h₁ 1
  have eq4 := h₁ 2
  have eq5 := h₁ 3
  have eq6 := h₀ 1
  have eq7 := h₀ 2
  have eq8 := h₀ 3
  have eq9 := h₁ 4
  have eq10 := h₁ 5
  have eq11 := h₀ 4
  norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 eq11
  have h7_8 : f (f 0 + 3) = 7 := by
    omega
  have h7_8' : f (f 0 + 3) = 8 := by
    have eq6' : f (f 1 + 3) = 8 := by
      omega
    have h1_f0 : f 1 = f 0 := by
      omega
    rw [show f 1 = f 0 by omega] at eq6'
    linarith [eq6']
    <;> omega
  omega