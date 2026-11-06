import Mathlib

theorem algebra_297266 (k : ℝ) (h : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    3*(x^2+3*x+4) = x*(2-x)*(2+k) ∧ 3*(y^2+3*y+4) = y*(2-y)*(2+k) ∧
    3*(z^2+3*z+4) = z*(2-z)*(2+k) ∧ x^2+y^2 = z^2) :
    k = 20 := by
  rcases h with ⟨x, y, z, h1, h2, h3, h4, h5, h6, h7⟩
  have eq1 : (k + 5) * x^2 + (5 - 2 * k) * x + 12 = 0 := by
    nlinarith
  have eq2 : (k + 5) * y^2 + (5 - 2 * k) * y + 12 = 0 := by
      nlinarith
  have eq3 : (k + 5) * z^2 + (5 - 2 * k) * z + 12 = 0 := by
      nlinarith
  have eq4 : (k + 5) * (x^2 - y^2) + (5 - 2 * k) * (x - y) = 0 := by 
    nlinarith [eq1, eq2]
  have eq5 : (x - y) * ( (k + 5) * (x + y) + (5 - 2 * k) ) = 0 := by
    ring_nf at eq4 ⊢
    <;> nlinarith
  cases (mul_eq_zero.mp eq5) with
  | inl h8 =>
    exfalso
    exact h1 (by linarith)
  | inr h9 =>
    have eq6 : (k + 5) * (x^2 - z^2) + (5 - 2 * k) * (x - z) = 0 := by 
      nlinarith [eq1, eq3]
    have eq7 : (x - z) * ( (k + 5) * (x + z) + (5 - 2 * k) ) = 0 := by
      ring_nf at eq6 ⊢
      <;> nlinarith
    cases (mul_eq_zero.mp eq7) with
    | inl h10 =>
      exfalso
      have h12 : z = x := by linarith
      have h13 : z = x := by linarith
      exfalso
      exact h3 (by linarith)
    | inr h11 =>
      have eq8 : (k + 5) * (y^2 - z^2) + (5 - 2 * k) * (y - z) = 0 := by 
        nlinarith [eq2, eq3]
      have eq9 : (y - z) * ( (k + 5) * (y + z) + (5 - 2 * k) ) = 0 := by
        ring_nf at eq8 ⊢
        <;> nlinarith
      cases (mul_eq_zero.mp eq9) with
      | inl h14 =>
        exfalso
        have h15 : y = z := by linarith
        exfalso
        exact h2 (by linarith)
      | inr h17 =>
        have eq10 : (k + 5) * (y - z) = 0 := by
          nlinarith [h9, h11, h17]
        have hk : k + 5 = 0 := by
          apply_fun (fun w => w / (y - z)) at eq10
          field_simp [(show y - z ≠ 0 by intro h'; apply h2; linarith)] at eq10
          linarith
        have h18 : k = -5 := by linarith
        have h19 : 5 - 2 * k = 0 := by
          rw [hk] at h9
          nlinarith
        linarith [h18, h19]