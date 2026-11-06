import Mathlib

theorem algebra_182829 (x y z : ℝ)
    (h1 : x * y + z = 40) (h2 : x * z + y = 51) (h3 : x + y + z = 19) :
    (x = 12 ∧ y = 3 ∧ z = 4) ∨ (x = 6 ∧ y = 5.4 ∧ z = 7.6) := by
  have h4 : z = 19 - x - y := by linarith
  rw [h4] at h1 h2
  have eq1 : x * y - x - y = 21 := by
    nlinarith
  have h5 : x * y = x + y + 21 := by
    nlinarith
  have h6 : x^2 - 18 * x + 72 = 0 := by
    nlinarith [h2, h5]
  have h7 : (x - 12) * (x - 6) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- Case x = 12
    have hx12 : x = 12 := by linarith
    have hy3 : y = 3 := by 
      rw [hx12] at h5
      nlinarith
    have hz4 : z = 4 := by 
      rw [hx12, hy3] at h4
      linarith
    left
    exact ⟨hx12, hy3, hz4⟩
  · -- Case x = 6
    have hx6 : x = 6 := by linarith
    have hy54 : y = 27 / 5 := by 
      rw [hx6] at h5
      nlinarith
    have hz76 : z = 38 / 5 := by 
      rw [hx6, hy54] at h4
      linarith
    right
    have hx6' : x = 6 := by linarith
    have hy54' : y = 5.4 := by
      rw [hy54]
      norm_num
    have hz76' : z = 7.6 := by 
      rw [hz76]
      norm_num
    exact ⟨hx6', hy54', hz76'⟩