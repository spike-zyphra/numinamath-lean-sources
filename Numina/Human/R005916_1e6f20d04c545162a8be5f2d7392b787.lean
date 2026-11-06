import Mathlib

open Complex Polynomial

lemma sum_sq_eq_zero (a b c : ℂ) (h1 : a^2 = b - c) (h2 : b^2 = c - a) (h3 : c^2 = a - b) :
    a^2 + b^2 + c^2 = 0 := by
  rw [h1, h2, h3]
  ring

lemma sum_cube_eq_zero (a b c : ℂ) (h1 : a^2 = b - c) (h2 : b^2 = c - a) (h3 : c^2 = a - b) :
    a^3 + b^3 + c^3 = 0 := by
  calc a^3 + b^3 + c^3
      = a * a^2 + b * b^2 + c * c^2 := by ring
  _   = a * (b - c) + b * (c - a) + c * (a - b) := by rw [h1, h2, h3]
  _   = a * b - a * c + b * c - b * a + c * a - c * b := by ring
  _   = (a * b - b * a) + (b * c - c * b) + (c * a - a * c) := by ring
  _   = 0 + 0 + 0 := by ring
  _   = 0 := by ring

lemma sum_fourth_pow (a b c : ℂ) (h1 : a^2 = b - c) (h2 : b^2 = c - a) (h3 : c^2 = a - b) (S : ℂ) (hS : S = a+b+c) :
    a^4 + b^4 + c^4 = -S^2 := by
  have h_sum_sq : a^2 + b^2 + c^2 = 0 := sum_sq_eq_zero a b c h1 h2 h3
  have h_sum_symm_prod : a*b + b*c + c*a = S^2 / 2 := by
    rw [hS]
    ring_nf
    field_simp [h_sum_sq]
    rw [add_assoc ((a * b + a * c) * 2)]
    rw [add_comm (a^2)]
    rw [add_assoc ((a*b+a*c)*2)]
    rw [add_assoc ((a*b+a*c)*2)]
    rw [add_assoc (b * c * 2)]
    rw [add_assoc (b * c * 2)]
    rw [h_sum_sq]
    rw [add_zero]
    ring
  have h_a4_a2 : a^4 + a^2 = -2 * b * c := by
    calc a^4 + a^2
        = a^2 * a^2 + a^2 := by ring
    _   = (b - c) * (b - c) + (b - c) := by rw [h1]
    _   = b^2 - 2 * b * c + c^2 + (b-c) := by ring
    _   = (c - a) - 2 * b * c + (a - b) + (b-c) := by rw [h2, h3]
    _   = c - a - 2*b*c + a - b + b - c := by ring
    _   = -2 * b * c := by ring
  have h_b4_b2 : b^4 + b^2 = -2 * c * a := by
    calc b^4 + b^2
        = b^2 * b^2 + b^2 := by ring
    _   = (c - a) * (c - a) + (c - a) := by rw [h2]
    _   = c^2 - 2 * c * a + a^2 + (c - a) := by ring
    _   = (a - b) - 2 * c * a + (b - c) + (c - a) := by rw [h3, h1]
    _   = a - b - 2*c*a + b - c + c - a := by ring
    _   = -2 * c * a := by ring
  have h_c4_c2 : c^4 + c^2 = -2 * a * b := by
    calc c^4 + c^2
        = c^2 * c^2 + c^2 := by ring
    _   = (a - b) * (a - b) + (a - b) := by rw [h3]
    _   = a^2 - 2 * a * b + b^2 + (a - b) := by ring
    _   = (b - c) - 2 * a * b + (c - a) + (a - b) := by rw [h1, h2]
    _   = b - c - 2*a*b + c - a + a - b := by ring
    _   = -2 * a * b := by ring
  calc a^4 + b^4 + c^4
      = a^4 + b^4 + c^4 + (a^2 + b^2 + c^2) := by rw [h_sum_sq, add_zero]
  _   = (a^4 + a^2) + (b^4 + b^2) + (c^4 + c^2) := by ring
  _   = (-2 * b * c) + (-2 * c * a) + (-2 * a * b) := by rw [h_a4_a2, h_b4_b2, h_c4_c2]
  _   = -2 * (a * b + b * c + c * a) := by ring
  _   = -2 * (S^2 / 2) := by rw [h_sum_symm_prod]
  _   = -S^2 := by field_simp; ring

lemma sum_fourth_pow_alt (a b c : ℂ) (h1 : a^2 = b - c) (h2 : b^2 = c - a) (h3 : c^2 = a - b) (S : ℂ) (hS : S = a+b+c) :
    a^4 + b^4 + c^4 = S^4 / 6 := by
  have h_sum_sq : a^2 + b^2 + c^2 = 0 := sum_sq_eq_zero a b c h1 h2 h3
  have h_sum_symm_prod : a*b + b*c + c*a = S^2 / 2 := by
    rw [hS, add_sq (a+b) c,add_sq a b]
    field_simp
    have h_ab :a ^ 2 + 2 * a * b + b ^ 2 + 2 * (a + b) * c + c ^ 2 =  2 * a * b +2 * (a + b) * c+ (a ^ 2 +b ^ 2  + c ^ 2) := by ring_nf
    rw [h_ab]
    rw [h_sum_sq]
    simp
    ring_nf
  have h_prod : a * b * c = S^3 / 6 := by
    have h_sum_cube : a^3 + b^3 + c^3 = 0 := sum_cube_eq_zero a b c h1 h2 h3
    have h_all : a^3 +b^3 +c^3 -3*a*b*c =(a+b+c)*(a^2+b^2+c^2-(a*b+b*c+c*a)):= by ring_nf
    rw [h_sum_cube,←hS,h_sum_sq,h_sum_symm_prod] at h_all
    field_simp at h_all
    ring_nf at h_all
    field_simp
    exact h_all
  have h_symm_prod_sq : a^2*b^2 + b^2*c^2 + c^2*a^2 = -S^4 / 12 := by
    have h_f:a^2*b^2 + b^2*c^2 + c^2*a^2 = (a*b + b*c + c*a)^2 - 2*a*b*c*(a+b+c) :=by ring_nf
    calc a^2*b^2 + b^2*c^2 + c^2*a^2
        = (a*b + b*c + c*a)^2 - 2*a*b*c*(a+b+c) := by rw [h_f]
    _   = (a*b + b*c + c*a)^2 - 2*(a*b*c)*(a+b+c) := by ring_nf
    _   = (S^2/2)^2 - 2*(S^3/6)*S := by rw [h_sum_symm_prod, h_prod, hS]
    _   = S^4/4 - 2*S^4/6 := by ring
    _   = S^4/4 - S^4/3 := by ring
    _   = (3*S^4 - 4*S^4) / 12 := by field_simp; ring
    _   = -S^4 / 12 := by ring
  calc a^4 + b^4 + c^4
      = (a^2 + b^2 + c^2)^2 - 2*(a^2*b^2 + b^2*c^2 + c^2*a^2) := by ring_nf
  _   = 0^2 - 2*(-S^4/12) := by rw [h_sum_sq, h_symm_prod_sq]
  _   = 0 - (-S^4/6) := by ring
  _   = S^4 / 6 := by ring

theorem possible_values_of_sum (a b c : ℂ) (h1 : a^2 = b - c) (h2 : b^2 = c - a) (h3 : c^2 = a - b) :
    (a + b + c) = 0 ∨ (a + b + c)^2 = -6 := by
  let S := a + b + c
  have hS : S = a + b + c := rfl
  have h_sum_fourth_pow_eq_neg_S_sq : a^4 + b^4 + c^4 = -S^2 := sum_fourth_pow a b c h1 h2 h3 S hS
  have h_sum_fourth_pow_eq_S_fourth_div_6 : a^4 + b^4 + c^4 = S^4 / 6 := sum_fourth_pow_alt a b c h1 h2 h3 S hS
  have h_S_eqn : -S^2 = S^4 / 6 := by
    rw [← h_sum_fourth_pow_eq_neg_S_sq, ← h_sum_fourth_pow_eq_S_fourth_div_6]
  have h_S_eqn2 : S^4 + 6 * S^2 = 0 := by
    calc S^4 + 6 * S^2 = 6 * (S^4 / 6 + S^2) := by field_simp; ring
                _ = 6 * (-S^2 + S^2) := by rw [h_S_eqn]
                _ = 6 * 0 := by ring
                _ = 0 := by ring
  have h_S_eqn3 : S^2 * (S^2 + 6) = 0 := by
    calc S^2 * (S^2 + 6) = S^4 + 6 * S^2 := by ring
                      _ = 0 := h_S_eqn2
  rcases mul_eq_zero.mp h_S_eqn3 with hSsq_zero | hSsq_plus_6_zero
  · have hS_zero : S = 0 := by
      rw [pow_two] at hSsq_zero
      exact mul_self_eq_zero.mp hSsq_zero
    left
    exact hS_zero
  · right
    rw [add_comm] at hSsq_plus_6_zero
    exact eq_neg_of_add_eq_zero_right hSsq_plus_6_zero

example : (0 : ℂ) = 0 ∨ (0 : ℂ)^2 = -6 := by simp
example : (I * Real.sqrt 6)^2 = -6 := by
  simp [sq, I_mul_I]
  ring_nf
  simp
  norm_cast
  norm_num
example : (-I * Real.sqrt 6)^2 = -6 := by
  simp [sq, I_mul_I]
  ring_nf
  simp
  norm_cast
  norm_num

theorem algebra_610700 (a b c : ℂ) (h1 : a^2 = b - c) (h2 : b^2 = c - a) (h3 : c^2 = a - b) :
    (a + b + c) ∈ ({0, I * (Real.sqrt 6), -I * (Real.sqrt 6)} : Set ℂ) := by
  have h := possible_values_of_sum a b c h1 h2 h3
  let S := a + b + c
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases h with hS0 | hSsq
  ·
    left
    exact hS0
  ·
    have h_sol_sq : (I * ↑(Real.sqrt 6))^2 = (-6 : ℂ) := by
      rw [mul_comm]
      rw [mul_pow]
      simp [sq, I_mul_I]
      ring_nf
      norm_cast
      norm_num
    rw [← h_sol_sq] at hSsq
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hSsq
    rcases hSsq with h_pos | h_neg
    ·
      right
      left
      exact h_pos
    ·
      right
      right
      rw [neg_mul_eq_neg_mul] at h_neg
      exact h_neg