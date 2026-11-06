import Mathlib

theorem algebra_187203 {x y : ℝ} (hx : x ≠ y) (hy : y ≠ -x) (h1 : (x + y) / (x - y) + (x - y) / (x + y) = 13 / 6) (h2 : x * y = 5) :
    (x = 5 ∧ y = 1) ∨ (x = -5 ∧ y = -1) := by
  have h3 : x - y ≠ 0 := by intro h; apply hx; linarith
  have h4 : x + y ≠ 0 := by
    by_contra h
    have h6 : x = -y := by linarith
    rw [h6] at h2
    have : (-y) * y = 5 := by linarith
    have : y ^ 2 = -5 := by
      nlinarith
    have : y ^ 2 ≥ 0 := by 
      exact sq_nonneg y
    linarith
  have eq1 : (x + y) ^ 2 + (x - y) ^ 2 = (13 / 6) * ((x - y) * (x + y)) := by
    have h3' : x - y ≠ 0 := h3 
    have h4' : x + y ≠ 0 := h4 
    field_simp [h3', h4'] at h1 ⊢ 
    linarith
  have eq2 : 6 * ((x + y) ^ 2 + (x - y) ^ 2) = 13 * ((x - y) * (x + y)) := by 
    linarith [eq1]
  have eq3 : x ^ 2 = 25 * y ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by exact h3), sq_pos_of_ne_zero (show x + y ≠ 0 by exact h4), h2]
  have h5 : (x - 5 * y) * (x + 5 * y) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case x = 5y 
    have hx_eq : x = 5 * y := by linarith 
    rw [hx_eq] at h2 
    have h8 : (5 * y) * y = 5 := h2 
    have h9 : 5 * y ^ 2 = 5 := by nlinarith
    have h10 : y ^ 2 = 1 := by nlinarith 
    have h11 : y = 1 ∨ y = -1 := by
      rw [sq_eq_one_iff] at h10 
      exact h10 
    cases' h11 with hy1 hy2
    · -- y = 1
      have hx1 : x = 5 := by linarith [hx_eq, hy1]
      left 
      exact ⟨hx1, hy1⟩
    · -- y = -1 
      have hx2 : x = -5 := by linarith [hx_eq, hy2]
      right 
      exact ⟨hx2, by linarith [hy2]⟩
  · -- Case x = -5y 
    have hx_eq : x = -5 * y := by linarith 
    rw [hx_eq] at h2 
    have h8 : (-5 * y) * y = 5 := h2
    have h9 : -5 * y ^ 2 = 5 := by nlinarith
    have h10 : y ^ 2 = -1 := by nlinarith
    have h11 : y ^ 2 ≥ 0 := sq_nonneg y
    nlinarith