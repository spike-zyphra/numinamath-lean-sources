import Mathlib

theorem algebra_97442 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ 4 ∧ y ≠ 6) :
    2 / x + 3 / y = 1 / 2 ↔ 4 * y / (y - 6) = x := by
  constructor
  · -- Forward direction: assume $\frac{2}{x} + \frac{3}{y} = \frac{1}{2}$, prove $\frac{4y}{y-6} = x$
    intro h_eq
    have h1 : x ≠ 0 := hx
    have h2 : x ≠ 4 := hxy.1
    have h3 : y ≠ 0 := hy
    have h4 : y ≠ 6 := hxy.2
    have eq1 : 2 * y + 3 * x = (1 / 2) * x * y := by
      field_simp [(show x ≠ 0 by exact h1), (show y ≠ 0 by exact h3)] at h_eq ⊢
      nlinarith
    have eq2 : 4 * y + 6 * x = x * y := by
      nlinarith [eq1]
    -- Solving $4y + 6x = xy$ for $x$ gives $4y = x(y-6)$, thus $\frac{4y}{y-6} = x$
    have eq3 : x = 4 * y / (y - 6) := by
      have h5 : y - 6 ≠ 0 := by
        intro h_eq6
        apply h4
        linarith
      have eq4 : 4 * y + 6 * x = x * y := by
        nlinarith
      have eq5 : 4 * y = x * (y - 6) := by
        nlinarith [eq2]
      field_simp [(show y - 6 ≠ 0 by
        intro h_eq6
        apply h4 
        linarith
      )] at * 
      nlinarith [eq5]
    linarith [eq3] 
  · -- Backward direction: assume $\frac{4y}{y-6} = x$, prove $\frac{2}{x} + \frac{3}{y} = \frac{1}{2}$
    intro h_eq
    have h1 : x ≠ 0 := hx
    have h2 : x ≠ 4 := hxy.1
    have h3 : y ≠ 0 := hy
    have h4 : y ≠ 6 := hxy.2
    have eq1 : 4 * y + 6 * x = x * y := by
      have h5 : y - 6 ≠ 0 := by
        intro h_eq6
        apply h4
        linarith
      have eq2 : 4 * y = x * (y - 6) := by
        field_simp [(show y - 6 ≠ 0 by
          intro h_eq6
          apply h4 
          linarith
        )] at h_eq 
        nlinarith 
      nlinarith [eq2] 
    have eq2 : 2 * y + 3 * x = (1 / 2) * x * y := by
      nlinarith [eq1] 
    have eq3 : 2 / x + 3 / y = 1 / 2 := by
      field_simp [(show x ≠ 0 by exact h1), (show y ≠ 0 by exact h3)]
      nlinarith 
      <;> nlinarith [eq1]
    linarith [eq3]