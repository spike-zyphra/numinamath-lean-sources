import Mathlib

theorem calculus_17194 (A B C : ℝ × ℝ × ℝ)
    (h₁ : (B + C) / 2 = (1, 5, -1))
    (h₂ : (A + C) / 2 = (0, 4, -2))
    (h₃ : (A + B) / 2 = (2, 3, 4)) :
    A = (1, 2, 3) := by 
  have eq1 := congr_arg (λ (x : ℝ × ℝ × ℝ) => x.1) h₁
  have eq2 := congr_arg (λ (x : ℝ × ℝ × ℝ) => x.2.1) h₁
  have eq3 := congr_arg (λ (x : ℝ × ℝ × ℝ) => x.2.2) h₁

  have eq4 := congr_arg (λ (x : ℝ × ℝ × ℝ) => x.1) h₂
  have eq5 := congr_arg (λ (x : ℝ × ℝ × ℝ) => x.2.1) h₂
  have eq6 := congr_arg (λ (x : ℝ × ℝ × ℝ) => x.2.2) h₂

  have eq7 := congr_arg (λ (x : ℝ × ℝ × ℝ) => x.1) h₃
  have eq8 := congr_arg (λ (x : ℝ × ℝ × ℝ) => x.2.1) h₃
  have eq9 := congr_arg (λ (x : ℝ × ℝ × ℝ) => x.2.2) h₃

  simp [add_div, mul_add, mul_comm] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9

  have Ax_eq : A.1 = 1 := by 
    linarith

  have Ay_eq : A.2.1 = 2 := by
    linarith

  have Az_eq : A.2.2 = 3 := by
    linarith

  simp [Prod.ext_iff, Ax_eq, Ay_eq, Az_eq]
  <;> linarith