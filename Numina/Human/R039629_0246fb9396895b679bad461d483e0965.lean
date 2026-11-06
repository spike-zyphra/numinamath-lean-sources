import Mathlib

/- The sum of the zeros, the product of the zeros, and the sum of the coefficients of the function f(x)=ax²+bx+c are equal. 
Their common value must also be which of the following?
(A) the coefficient of x²
(B) the coefficient of x 
(C) the y-intercept of the graph of y=f(x)
(D) one of the x-intercepts of the graph of y=f(x)
(E) the mean of the x-intercepts of the graph of y=f(x) -/
theorem algebra_98155 {a b c : ℝ} (ha : a ≠ 0) (h : ∃ x1 x2, x1 ≠ x2 ∧ a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0 ∧ x1 + x2 = x1 * x2) :
a + b + c = a := by
  obtain ⟨x1, x2, dif, hx1, hx2, x1_e_x2⟩:= h 
  --rewrite the quadratic equations in order to apply Vieta
  have h : x1 ^ 2 - (- b / a) * x1 + (c / a) = 0 := by
    field_simp
    rw[mul_comm]
    exact hx1
  have l : x2 ^ 2 - (- b / a) * x2 + (c / a) = 0 := by
    field_simp
    rw[mul_comm]
    exact hx2
  have e : x1 ^ 2 = x1 * x1 := by linarith
  rw[e] at h
  --apply Vieta
  have h_vieta : ∃ y, y * y - (- b / a) * y + c / a = 0 ∧ x1 + y = - b / a ∧ x1 * y = c / a := by 
    apply vieta_formula_quadratic h
  obtain ⟨y, hy, k1, k2⟩:= h_vieta
  --since for a quaratic equations there are only two solutions then y = x2 is the other solution
  have y_eq_x2 : y = x2 := by
    have hyp : ∀ t : ℝ, t ^ 2 - (- b / a) * t + (c / a) = (t - x1) * (t - y) := by
      have s : ∀ t : ℝ, t ^ 2 - (x1 + y) * t + (x1 * y) = (t - x1) * (t - y) := by intro t; ring_nf
      rw[k1, k2] at s
      exact s
    specialize hyp x2
    rw[l] at hyp
    have kk : (x2 - x1) * (x2 - y) = 0 := by exact id (Eq.symm hyp)
    have m : (x2 - x1) = 0 ∨ (x2 - y) = 0 := by rw[mul_eq_zero] at kk; exact kk
    obtain m1|m2 := m
    · have u: x1 = x2 := by linarith
      contradiction
    · linarith
  --after substitution one gets that b=-c
  rw[y_eq_x2] at k1 k2
  rw[k1, k2] at x1_e_x2
  have hyp: -b = c := by 
    field_simp at x1_e_x2
    have j : (c + b) * a = 0 := by linarith
    have jj : c + b = 0 ∨ a = 0 := by rw[mul_eq_zero] at j; exact j
    obtain jj1|jj2 := jj
    · linarith
    · contradiction
  --this directly implies the claim
  rw[← hyp]
  ring_nf