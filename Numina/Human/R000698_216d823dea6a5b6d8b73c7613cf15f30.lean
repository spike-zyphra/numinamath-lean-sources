import Mathlib

/- The sum of two fractions is $\frac{11}{12}$ and their product is $\frac{1}{6}$. What is the lesser of the two fractions? Express your answer as a common fraction. -/
theorem algebra_14036 {x y : ℚ} (hx : x + y = 11 / 12) (hy : x * y = 1 / 6) :
    min x y = 1 / 4 := by
  have h : x + y = 11 / 12 := hx
  have h' : x * y = 1 / 6 := hy
  have h'' : x ≤ y ∨ y ≤ x := le_total x y
  cases' h'' with h'' h''
  next =>
    rw [min_eq_left h'']
    nlinarith
  next =>
    rw [min_eq_right h'']
    nlinarith