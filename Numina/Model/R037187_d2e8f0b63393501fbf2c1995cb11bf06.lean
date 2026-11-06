import Mathlib

theorem algebra_187153 :
    {(x, y) : ℝ × ℝ | (x - y) * (x ^ 2 - y ^ 2) = 45 ∧ x + y = 5} = {(4, 1), (1, 4)} := by
  ext ⟨x, y⟩
  simp [-mul_add, -add_mul]
  constructor
  · -- Assume (x, y) is in the left side, need to prove (4,1), (1,4)
    rintro ⟨h1, h2⟩
    have h3 : y = 5 - x := by linarith
    rw [h3] at h1
    have h4 : (x - 4) * (x - 1) = 0 := by
      nlinarith [h1]
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- x = 4
      have hx : x = 4 := by linarith
      have hy : y = 1 := by linarith [h3, hx]
      simp [hx, hy]
    · -- x = 1
      have hx : x = 1 := by linarith
      have hy : y = 4 := by linarith [h3, hx]
      simp [hx, hy]
  · -- Assume (x,y) is (4,1) or (1,4), need to prove the system
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (4,1)
      constructor
      · norm_num
      · norm_num
    · -- (1,4)
      constructor
      · norm_num
      · norm_num