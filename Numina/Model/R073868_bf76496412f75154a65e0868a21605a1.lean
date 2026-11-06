import Mathlib

theorem algebra_35490 {p q : ℝ} (h : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x^3 + p * x + q = 0 ∧ y^3 + p * y + q = 0 ∧ z^3 + p * z + q = 0) :
    p < 0 := by
  rcases h with ⟨x, y, z, hxy, hyz, hzx, hx, hy, hz⟩
  have h1 : x^3 + p * x + q = 0 := hx
  have h2 : y^3 + p * y + q = 0 := hy
  have h3 : z^3 + p * z + q = 0 := hz
  have eq1 : x^3 + p * x + q - (y^3 + p * y + q) = 0 := by linarith
  have eq2 : (x - y) * (x^2 + x * y + y^2 + p) = 0 := by
    ring_nf at eq1 ⊢
    linarith
  have h4 : x^2 + x * y + y^2 + p = 0 := by
    apply_fun (λ w => w / (x - y)) at eq2
    field_simp [sub_ne_zero.mpr hxy] at eq2
    linarith
  have eq3 : y^3 + p * y + q - (z^3 + p * z + q) = 0 := by linarith
  have eq4 : (y - z) * (y^2 + y * z + z^2 + p) = 0 := by
    ring_nf at eq3 ⊢
    linarith
  have h5 : y^2 + y * z + z^2 + p = 0 := by
    apply_fun (λ w => w / (y - z)) at eq4
    field_simp [sub_ne_zero.mpr hyz] at eq4
    linarith
  have eq5 : z^3 + p * z + q - (x^3 + p * x + q) = 0 := by linarith
  have eq6 : (z - x) * (z^2 + z * x + x^2 + p) = 0 := by
    ring_nf at eq5 ⊢
    linarith
  have h6 : z^2 + z * x + x^2 + p = 0 := by
    apply_fun (λ w => w / (z - x)) at eq6
    field_simp [sub_ne_zero.mpr hzx] at eq6
    linarith
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hxy), sq_pos_of_ne_zero (sub_ne_zero.mpr hyz), sq_pos_of_ne_zero (sub_ne_zero.mpr hzx), 
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
            sq_nonneg (x + y + z)]