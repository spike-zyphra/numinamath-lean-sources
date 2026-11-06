import Mathlib

theorem algebra_155309 (f : ℝ → ℝ) (hf : f = fun x => x^2 - 4 * x - 1)
    (A B C : ℝ × ℝ) (hA : A.1 ≠ B.1) (hB : B.1 ≠ C.1) (hC : C.1 ≠ A.1)
    (hC1 : C.1 = 5) (hA1 : A.2 = f A.1) (hB1 : B.2 = f B.1) (hAB : A.2 = B.2) :
    (A.1 + B.1 + C.1) / 3 = 3 := by
  have h1 : ∀ x, f x = x^2 - 4 * x - 1 := by
    intro x
    rw [hf]
  rw [h1] at hA1 hB1
  have h_eq : A.1 ^ 2 - 4 * A.1 - 1 = B.1 ^ 2 - 4 * B.1 - 1 := by
    linarith
  have h_sum : A.1 + B.1 = 4 := by
    have h_neq : A.1 ≠ B.1 := hA
    have h2 : (A.1 - B.1) * (A.1 + B.1 - 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- $A.1 - B.1 = 0$, so $A.1 = B.1$ which is a contradiction
      have h_eq : A.1 = B.1 := by linarith
      contradiction
    · -- $A.1 + B.1 - 4 = 0$, so $A.1 + B.1 = 4$
      linarith
  have hC2 : C.1 = 5 := hC1
  linarith [h_sum, hC2]