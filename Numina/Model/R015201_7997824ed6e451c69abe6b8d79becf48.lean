import Mathlib

theorem algebra_223878 :
    {(x, y) : ℝ × ℝ | x = x ^ 2 + y ^ 2 ∧ y = 2 * x * y}.encard = 4 := by 
  have h1 : {(x, y) : ℝ × ℝ | x = x ^ 2 + y ^ 2 ∧ y = 2 * x * y} = {(0, 0), (1, 0), (1 / 2, 1 / 2), (1 / 2, -1 / 2)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Forward implication: both equations imply membership in the claimed set.
      rintro ⟨h1, h2⟩
      have h3 : y * (1 - 2 * x) = 0 := by 
        linarith 
      cases' (mul_eq_zero.mp h3) with hy hx
      · -- When y = 0:
        have hy' : y = 0 := by 
          linarith 
        have h4 : x = x ^ 2 + y ^ 2 := by linarith 
        rw [hy'] at h4 
        have h5 : x * (x - 1) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.mp h5) with hx1 hx2 
        · -- When x = 0:
          have hx' : x = 0 := by 
            linarith 
          simp [hx', hy']
        · -- When x - 1 = 0:
          have hx' : x = 1 := by 
            linarith 
          simp [hx', hy']
      · -- When 1 - 2 * x = 0:
        have hx' : x = 1 / 2 := by 
          linarith 
        have h4 : x = x ^ 2 + y ^ 2 := by linarith 
        rw [hx'] at h4 
        have h5 : y ^ 2 = 1 / 4 := by 
          nlinarith 
        have h6 : y = 1 / 2 ∨ y = -1 / 2 := by 
          have h7 : (y - 1 / 2) * (y + 1 / 2) = 0 := by 
            nlinarith 
          cases' (mul_eq_zero.mp h7) with hy1 hy2 
          · -- y - 1 / 2 = 0 
            left 
            linarith 
          · -- y + 1 / 2 = 0 
            right 
            linarith 
        cases h6 with 
        | inl hy' => 
          simp [hx', hy']
        | inr hy' => 
          simp [hx', hy']
    · -- Backward implication: membership in claimed set means equations hold.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (0, 0)
        constructor <;> norm_num 
      · -- Check (1, 0)
        constructor <;> norm_num 
      · -- Check (1/2, 1/2)
        constructor <;> norm_num 
      · -- Check (1/2, -1/2)
        constructor <;> norm_num 
  rw [h1] 
  rw [Set.encard]
  simp [Set.ncard]
  <;> norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton, Prod.ext_iff]