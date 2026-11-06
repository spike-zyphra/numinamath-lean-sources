import Mathlib

theorem algebra_151327 (c : ℝ) :
    ¬∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      (x ^ 3 + 4 * x ^ 2 + 6 * x + c = 0) ∧
      (y ^ 3 + 4 * y ^ 2 + 6 * y + c = 0) ∧
      (z ^ 3 + 4 * z ^ 2 + 6 * z + c = 0) := by
  rintro ⟨x, y, z, h1, h2, h3, h4, h5, h6⟩
  have eq1 : (x - y) * (x ^ 2 + x * y + y ^ 2 + 4 * (x + y) + 6) = 0 := by
    nlinarith [h4, h5]
  have h7 : x ^ 2 + x * y + y ^ 2 + 4 * (x + y) + 6 = 0 := by
    apply_fun (fun w => w / (x - y)) at eq1
    field_simp [(show x - y ≠ 0 by intro h; apply h1; linarith)] at eq1 ⊢
    linarith
  have eq2 : (y - z) * (y ^ 2 + y * z + z ^ 2 + 4 * (y + z) + 6) = 0 := by
    nlinarith [h5, h6]
  have h8 : y ^ 2 + y * z + z ^ 2 + 4 * (y + z) + 6 = 0 := by
    apply_fun (fun w => w / (y - z)) at eq2
    field_simp [(show y - z ≠ 0 by intro h; apply h2; linarith)] at eq2 ⊢
    linarith
  have eq3 : (x - z) * (x + y + z + 4) = 0 := by
    nlinarith [h7, h8]
  have h9 : x + y + z + 4 = 0 := by
    apply (mul_left_inj' (show x - z ≠ 0 by intro h; apply h3; linarith)).mp
    linarith
  have eq4 : (x - z) * (x ^ 2 + x * z + z ^ 2 + 4 * (x + z) + 6) = 0 := by
    nlinarith [h4, h6]
  have h10 : x ^ 2 + x * z + z ^ 2 + 4 * (x + z) + 6 = 0 := by
    apply (mul_left_inj' (show x - z ≠ 0 by intro h; apply h3; linarith)).mp
    linarith
  nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by intro h; apply h1; linarith),
    sq_pos_of_ne_zero (show y - z ≠ 0 by intro h; apply h2; linarith),
    sq_pos_of_ne_zero (show x - z ≠ 0 by intro h; apply h3; linarith),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]