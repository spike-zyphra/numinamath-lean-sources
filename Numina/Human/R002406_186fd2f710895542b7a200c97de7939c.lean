import Mathlib.Tactic

/-
 PROBLEM:
 Suppose that $\tfrac{2}{3}$ of $10$ bananas are worth as much as $8$ oranges. How many oranges are worth as much as $\tfrac{1}{2}$ of $5$ bananas?
 $\mathrm{(A)}\ 2\qquad\mathrm{(B)}\ \frac{5}{2}\qquad\mathrm{(C)}\ 3\qquad\mathrm{(D)}\ \frac{7}{2}\qquad\mathrm{(E)}\ 4$
-/

theorem alg_1191
  (b o : ℕ)
  (h₁ : (2 : ℚ) / 3 * 10 * b = 8 * o) :
  (1 : ℚ) / 2 * 5 * b = 3 * o := by
    -- send denominator to other side
    field_simp at h₁
    -- isolate b
    have banana : b = ((8 : ℚ) * o * 3)/(2 * 10) := by
      refine (eq_div_iff_mul_eq ?hc).mpr ?_
      native_decide
      rw [mul_comm] at h₁
      exact h₁
    rw [banana]
    -- final calculation
    ring