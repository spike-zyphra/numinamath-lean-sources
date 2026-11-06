import Mathlib

/-
The polynomial p(x)=x^3 + a * x^2 + b * x + c
has the property that the average of its zeros,
the product of its zeros,
and the sum of its coefficients are all equal.
The y-intercept of the graph of y=p(x) is 2.
What is b?

(A) −11(B) −10(C) −9(D) 1(E) 5
-/

theorem algebra_95136 {a b c : ℝ} {p : ℝ → ℝ} (hp : p = fun x => x^3 + a * x^2 + b * x + c)
(hzeros : ∃ x1 x2 x3,
 (x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1) ∧
 (x1 + x2 + x3 = 3 * (x1 * x2 * x3)) ∧
 (x1 * x2 * x3 = a + b + c + 1) ∧
 ((x1 * x2 * x3) = -c) ∧
 (-(x1 + x2 + x3) = a))
(hyintercept : p 0 = 2) : b = -11 := by
  -- Use the y-intercept to conclude the value of c = 2
  have hc: c = 2 := by
    rw [hp] at hyintercept
    simp at hyintercept
    exact hyintercept
  rw [hc] at hp hzeros
  -- use the linear system of equations in a and b to conclude the value of b
  obtain ⟨x1, x2, x3, ⟨ h1, ⟨ h2, ⟨ h3, ⟨ h4, h5⟩⟩⟩⟩ ⟩ := hzeros
  linarith