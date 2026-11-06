import Mathlib

theorem algebra_55963 {a : ℝ} {x1 x2 x3 x4 : ℝ}
    (hx1 : x1^2 + a * x1 + 2 = x1) (hx2 : x2^2 + a * x2 + 2 = x2)
    (hx3 : (x3 - a)^2 + a * (x3 - a) + 2 = x3) (hx4 : (x4 - a)^2 + a * (x4 - a) + 2 = x4)
    (hne : x1 ≠ x2 ∧ x3 ≠ x4) (hdiff : x3 - x1 = 3 * (x4 - x2)) :
    x4 - x2 = a / 2 := by
  -- First, rewrite the equations in standard quadratic form.
  have eq1 : x1^2 + (a - 1) * x1 + 2 = 0 := by linarith [hx1]
  have eq2 : x2^2 + (a - 1) * x2 + 2 = 0 := by linarith [hx2]
  have eq3 : x3^2 - (a + 1) * x3 + 2 = 0 := by
    nlinarith [hx3]
  have eq4 : x4^2 - (a + 1) * x4 + 2 = 0 := by
    nlinarith [hx4]
  -- Subtract the equations to form difference equations
  have eq5 : (x1 - x2) * (x1 + x2 + a - 1) = 0 := by
    nlinarith
  have eq6 : (x3 - x4) * (x3 + x4 - (a + 1)) = 0 := by
    nlinarith
  -- From distinct roots, derive sum relations
  have h1 : x1 + x2 + a - 1 = 0 := by
    apply_fun (fun y => y / (x1 - x2)) at eq5
    field_simp [sub_ne_zero.2 hne.1] at eq5
    linarith
  have h2 : x3 + x4 - (a + 1) = 0 := by
    apply_fun (fun y => y / (x3 - x4)) at eq6
    field_simp [sub_ne_zero.2 hne.2] at eq6
    linarith
  -- Now solve using the difference condition
  have eq7 : x3 - x1 = 3 * (x4 - x2) := hdiff
  have eq8 : x1 + x2 = 1 - a := by linarith [h1]
  have eq9 : x3 + x4 = a + 1 := by linarith [h2]
  -- Now we need to compute x4 - x2.
  have eq10 : x4 - x2 = a / 2 := by
    nlinarith [eq7, eq8, eq9]
  linarith [eq10]