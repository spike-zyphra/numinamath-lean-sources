import Mathlib

theorem algebra_189827 {a : ℝ} (ha : ∃ x1 x2, x1 ≠ x2 ∧
    (1/3)*x1^2+(a+1/2)*x1+(a^2+a)=0 ∧
    (1/3)*x2^2+(a+1/2)*x2+(a^2+a)=0 ∧
    x1^3+x2^3=3*(x1*x2)) :
    a ≤ -1/4 := by

  rcases ha with ⟨x1, x2, hx12, h1, h2, h3⟩

  have eq1 : (x1 - x2) * ( (1/3) * (x1 + x2) + (a + 1/2) ) = 0 := by
    have eq2 : (1/3)*x1^2 + (a + 1/2)*x1 + (a^2 + a) - ((1/3)*x2^2 + (a + 1/2)*x2 + (a^2 + a)) = 0 := by
      linarith [h1, h2]
    have eq3 : (1/3)*x1^2 + (a + 1/2)*x1 + (a^2 + a) - ((1/3)*x2^2 + (a + 1/2)*x2 + (a^2 + a)) =
        (x1 - x2) * ((1/3) * (x1 + x2) + (a + 1/2)) := by
      ring
    rw [eq3] at eq2
    linarith

  cases' (mul_eq_zero.1 eq1) with h4 h5
  · -- x1 - x2 = 0 
    exfalso 
    apply hx12 
    linarith
  · -- (1/3)* (x1 + x2) + (a + 1/2) = 0 
    have hsum : x1 + x2 = -3*a - 3/2 := by
      linarith
    have hprod : x1 * x2 = 3*a^2 + 3*a := by
      nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
        intro h'
        apply hx12
        linarith
      ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 - (-3*a - 3/2)), hsum]
    rw [show x1^3 + x2^3 = (x1 + x2)^3 - 3*(x1*x2)*(x1 + x2) by ring] at h3 
    rw [hprod] at h3
    rw [hsum] at h3 
    have eq2 : (a + 1/4) * (a + 3/2) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.1 eq2) with h4 h5
    · -- case a + 1/4 = 0 
      linarith 
    · -- case a + 3/2 = 0 
      nlinarith