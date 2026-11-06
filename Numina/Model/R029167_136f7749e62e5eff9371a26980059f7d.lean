import Mathlib

theorem algebra_47 {a b : ℝ} (ha : a ≠ 0) (hvertex : ∃ x y, x = -b / (2 * a) ∧ y = a * (-b / (2 * a))^2 + b * (-b / (2 * a)) + 1 ∧ x < 0 ∧ y > 0)
    (hpoint : a + b + 1 = 0) (hint : ∃ m : ℤ, a - b = m) :
    a * b = 1 / 4 := by
  rcases hvertex with ⟨x, y, hx_eq, hy_eq, hx_lt, hy_gt⟩
  rcases hint with ⟨m, hm⟩
  have h1 : b = -1 - a := by linarith
  have h2 : -b / (2 * a) = (1 + a) / (2 * a) := by 
    rw [show b = -1 - a by linarith]
    field_simp [ha]
    <;> ring
  have hx_lt3 : (1 + a) / (2 * a) < 0 := by
    rw [← h2]
    have hx1 : x = -b / (2 * a) := hx_eq
    linarith [hx1, hx_lt]
  have h5' : 1 + a > 0 ∧ (2 * a) < 0 ∨ 1 + a < 0 ∧ (2 * a) > 0 := by 
    apply div_neg_iff.mp
    linarith
  rcases h5' with h6 | h7
  · -- Case 1: 1 + a > 0 and 2 * a < 0
    have ha1 : a > -1 := by linarith
    have ha2 : a < 0 := by linarith
    have hm2 : 2 * a + 1 = (m : ℝ) := by 
      rw [show b = -1 - a by linarith] at hm
      nlinarith
    have hm4 : m = 0 := by
      have h7 : (m : ℝ) = (2 * a + 1 : ℝ) := by 
        linarith [hm2]
      have h8 : -1 < a := by linarith
      have h9 : a < 0 := by linarith
      have h10 : -1 < (2 * a + 1 : ℝ) := by nlinarith
      have h11 : (2 * a + 1 : ℝ) < 1 := by nlinarith
      have hm_int : m = 0 := by
        have h13 : (m : ℝ) > -1 := by nlinarith [h7, h10]
        have h14 : (m : ℝ) < 1 := by nlinarith [h7, h11]
        have h15 : m > -1 := by
          by_contra h
          push_neg at h
          have : (m : ℝ) ≤ (-1 : ℝ) := by 
            exact_mod_cast h
          nlinarith
        have h16 : m < 1 := by
          by_contra h
          push_neg at h
          have : (m : ℝ) ≥ (1 : ℝ) := by
            exact_mod_cast h
          nlinarith
        interval_cases m <;> norm_num at h7 <;> nlinarith
      exact_mod_cast hm_int
    have hm5 : (m : ℝ) = 0 := by 
      exact_mod_cast hm4
    have ha2 : a = -1 / 2 := by 
      nlinarith [hm5, hm2]
    have hb2 : b = -1 / 2 := by 
      rw [ha2] at h1
      linarith
    rw [ha2, hb2]
    norm_num
  · -- Case 2: impossible
    exfalso 
    nlinarith