import Mathlib
open Real
theorem algebra_232861 : {(x, y, z) : ℝ × ℝ × ℝ | x + y + z = 0 ∧ x ^ 2 + y ^ 2 - z ^ 2 = 20 ∧ x ^ 4 + y ^ 4 - z ^ 4 = 560} = {(5, -2, -3), (-2, 5, -3), (2, -5, 3), (-5, 2, 3)}:= by

  ext ⟨x, y, z⟩
  simp
  constructor
  · -- First direction: system to roots
    rintro ⟨h₁, h₂, h₃⟩

    have h4 : z = -x - y := by linarith
    rw [h4] at h₂ h₃

    have h5 : x * y = -10 := by 
      nlinarith [h₂]

    have h6 : (x + y) ^ 2 = 9 := by 
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x + y), sq_nonneg (x - y), h5, sq_nonneg (x + 5), sq_nonneg (y + 2) ]

    have h7 : x + y = 3 ∨ x + y = -3 := by
      have : (x + y) ^ 2 - 9 = 0 := by linarith
      have : (x + y - 3) * (x + y + 3) = 0 := by nlinarith
      cases (mul_eq_zero.1 this) with
      | inl h => 
        left
        linarith
      | inr h => 
        right
        linarith

    cases h7 with
    | inl h7 =>
      have h8 : y = 3 - x := by
        linarith [h7]
      rw [h8] at h5
      have : (x - 5) * (x + 2) = 0 := by 
        nlinarith 
      cases (mul_eq_zero.1 this) with
      | inl h10 => 
        have hx : x = 5 := by
          nlinarith [h10]
        have hy : y = -2 := by
          nlinarith [h7, hx]
        have hz : z = -3 := by 
          nlinarith [show z = -x - y from by linarith, hx, hy]
        simp [hx, hy, hz]
      | inr h11 => 
        have hx : x = -2 := by
          nlinarith [h11]
        have hy : y = 5 := by
          nlinarith [h7, hx]
        have hz : z = -3 := by 
          nlinarith [show z = -x - y from by linarith, hx, hy]
        simp [hx, hy, hz]
    
    | inr h7 =>
      have h8 : y = -3 - x := by
        linarith [h7]
      rw [h8] at h5
      have : (x - 2) * (x + 5) = 0 := by 
        nlinarith 
      cases (mul_eq_zero.1 this) with
      | inl h10 => 
        have hx : x = 2 := by
          nlinarith [h10]
        have hy : y = -5 := by
          nlinarith [h7, hx]
        have hz : z = 3 := by 
          nlinarith [show z = -x - y from by linarith, hx, hy]
        simp [hx, hy, hz]
      | inr h11 => 
        have hx : x = -5 := by
          nlinarith [h11]
        have hy : y = 2 := by
          nlinarith [h7, hx]
        have hz : z = 3 := by 
          nlinarith [show z = -x - y from by linarith, hx, hy]
        simp [hx, hy, hz]

  · -- Second direction: roots satisfy the system
    rintro (h | h | h | h)
    · -- Verify first root
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Verify second root
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Verify third root
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Verify fourth root
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num