import Mathlib

theorem algebra_147536 {A B : ℤ} (h₀ : A + B = 1812) (h₁ : A / B = 7 ∧ A % B = 4) :
    max A B - min A B = 1360 := by
  have h2 : B ≠ 0 := by
    by_contra h
    have h3 : B = 0 := by linarith
    rw [h3] at h₁
    norm_num at h₁
  have h3 : A = 7 * B + 4 := by
    rw [← Int.ediv_add_emod A B, h₁.1, h₁.2]
    all_goals
      ring
  have h4 : 8 * B = 1808 := by
    omega
  have h5 : B = 226 := by
    omega
  have h6 : A = 1586 := by
    rw [h5] at h3
    linarith
  rw [h5, h6]
  all_goals
    norm_num [max_eq_left_of_lt, min_eq_right_of_lt]