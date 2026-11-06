import Mathlib

theorem algebra_166233 : {(x, y, z) : ℝ×ℝ×ℝ | x + y + z = 6 ∧ x * (y + z) = 5 ∧ y * (x + z) = 8} = {(5,2,-1), (5,4,-3), (1,2,3), (1,4,1)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume (x, y, z) in the left side, prove in the right side
    rintro ⟨h1, h2, h3⟩
    have hz : z = 6 - x - y := by 
      linarith 
    rw [hz] at h2
    have h2' : x ^ 2 - 6 * x + 5 = 0 := by 
      nlinarith 
    rw [hz] at h3 
    have h3' : y ^ 2 - 6 * y + 8 = 0 := by 
      nlinarith 
    have hx : (x - 5) * (x - 1) = 0 := by 
      nlinarith [h2']
    have hy : (y - 2) * (y - 4) = 0 := by 
      nlinarith [h3']
    cases' (mul_eq_zero.mp hx) with hx1 hx2 
    · -- Case x = 5
      have hx5 : x = 5 := by linarith
      cases' (mul_eq_zero.mp hy) with hy1 hy2 
      · -- Case y = 2
        have hy2' : y = 2 := by linarith 
        have hz1 : z = -1 := by
          rw [hx5, hy2'] at h1 
          linarith 
        simp [hx5, hy2', hz1]
      · -- Case y = 4
        have hy4' : y = 4 := by linarith
        have hz3 : z = -3 := by
          rw [hx5, hy4'] at h1 
          linarith 
        simp [hx5, hy4', hz3]
    · -- Case x = 1
      have hx1' : x = 1 := by linarith 
      cases' (mul_eq_zero.mp hy) with hy1 hy2
      · -- Case y = 2
        have hy2' : y = 2 := by linarith
        have hz3 : z = 3 := by 
          rw [hx1', hy2'] at h1 
          linarith 
        simp [hx1', hy2', hz3]
      · -- Case y = 4
        have hy4' : y = 4 := by linarith
        have hz1 : z = 1 := by 
          rw [hx1', hy4'] at h1 
          linarith 
        simp [hx1', hy4', hz1]
  · -- Assume (x, y, z) in the right side, prove in the left side
    rintro (h | h | h | h)
    · -- (5, 2, -1)
      rcases h with ⟨rfl, rfl, rfl⟩ 
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- (5, 4, -3)
      rcases h with ⟨rfl, rfl, rfl⟩ 
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- (1, 2, 3)
      rcases h with ⟨rfl, rfl, rfl⟩ 
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- (1, 4, 1)
      rcases h with ⟨rfl, rfl, rfl⟩ 
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num