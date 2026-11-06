import Mathlib

theorem number_theory_248298 : {(x, y, z, t) : ℤ×ℤ×ℤ×ℤ | x * z - 2 * y * t = 3 ∧ x * t + y * z = 1} = {(1, 0, 3, 1), (-1, 0, -3, -1), (3, 1, 1, 0), (-3, -1, -1, 0)} := by
  ext ⟨x, y, z, t⟩
  simp
  constructor
  · -- First direction: system → finite points
    rintro ⟨h₁, h₂⟩
    have eq3 : ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) * ((z : ℤ) ^ 2 + 2 * (t : ℤ) ^ 2) = 11 := by
      have eq4 : (x * z - 2 * y * t : ℤ) ^ 2 + 2 * (x * t + y * z : ℤ) ^ 2 = ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) * ((z : ℤ) ^ 2 + 2 * (t : ℤ) ^ 2) := by
        nlinarith [sq_nonneg (x * z), sq_nonneg (y * t), sq_nonneg (x * t), sq_nonneg (y * z), sq_nonneg (x * y), sq_nonneg (z * t)]
      have eq5 : (x * z - 2 * y * t : ℤ) ^ 2 + 2 * (x * t + y * z : ℤ) ^ 2 = 11 := by
        rw [show (x * z - 2 * y * t : ℤ) = 3 by linarith [h₁], 
          show (x * t + y * z : ℤ) = 1 by linarith [h₂]]
        norm_num
      nlinarith [eq5, eq4]
    have h6 : ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) = 1 ∨ ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) = 11 := by
      have h5 : ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) ∣ 11 := by
        use ((z : ℤ) ^ 2 + 2 * (t : ℤ) ^ 2)
        all_goals nlinarith
      have h7 : ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) ∣ 11 := h5
      have h9 : ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) ≥ 1 := by 
        nlinarith [sq_nonneg x, sq_nonneg y]
      have h10 : ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) = 1 ∨ ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) = 11 := by 
        have h9 : ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) ∣ 11 := h7
        have h12 : ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) ≤ 11 := by 
          exact Int.le_of_dvd (by norm_num) h9
        interval_cases h : ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) <;> tauto
      assumption
    rcases h6 with (h8 | h8)
    · -- Case where x² + 2 y² = 1
      have h9 : (x ^ 2 + 2 * y ^ 2 : ℤ) = 1 := by 
        nlinarith
      have h10 : (z ^ 2 + 2 * t ^ 2 : ℤ) = 11 := by 
        have eq4 : ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) * ((z : ℤ) ^ 2 + 2 * (t : ℤ) ^ 2) = 11 := eq3
        rw [h9] at eq4
        nlinarith
      have h11 : y = 0 := by
        have h11 : y ^ 2 = 0 := by
          nlinarith [sq_nonneg y, sq_nonneg x]
        have h12 : y = 0 := by
          nlinarith
        assumption
      have h12 : x ^ 2 = 1 := by
        nlinarith [sq_nonneg x, h11]
      have h13 : x = 1 ∨ x = -1 := by
        have h14 : x ^ 2 = 1 := by
          nlinarith
        have h15 : x = 1 ∨ x = -1 := by
          rw [sq_eq_one_iff] at h14
          tauto
        assumption
      rcases h13 with (h14 | h14)
      · -- x = 1
        have ht1 : t = 1 := by
          rw [h14] at h₂
          rw [h11] at h₂
          nlinarith
        have hz1 : z = 3 := by
          rw [h14] at h₁
          rw [h11] at h₁
          nlinarith
        simp [h14, h11, hz1, ht1]
      · -- x = -1
        have ht1 : t = -1 := by
          rw [h14] at h₂
          rw [h11] at h₂
          nlinarith
        have hz1 : z = -3 := by
          rw [h14] at h₁
          rw [h11] at h₁
          nlinarith
        simp [h14, h11, hz1, ht1]
    · -- Case where x² + 2 y² = 11
      have h9 : (x ^ 2 + 2 * y ^ 2 : ℤ) = 11 := by 
        nlinarith
      have h10 : (z ^ 2 + 2 * t ^ 2 : ℤ) = 1 := by 
        have eq4 : ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) * ((z : ℤ) ^ 2 + 2 * (t : ℤ) ^ 2) = 11 := eq3
        rw [h9] at eq4
        nlinarith
      have h11 : t = 0 := by
        have h11 : t ^ 2 = 0 := by
          nlinarith [sq_nonneg t, sq_nonneg z]
        have h12 : t = 0 := by
          nlinarith
        assumption
      have h12 : z ^ 2 = 1 := by
        nlinarith [sq_nonneg z, h11]
      have h13 : z = 1 ∨ z = -1 := by
        have h14 : z ^ 2 = 1 := by
          nlinarith
        have h15 : z = 1 ∨ z = -1 := by
          rw [sq_eq_one_iff] at h14
          tauto
        assumption
      rcases h13 with (h14 | h14)
      · -- z = 1
        have hx1 : x = 3 := by
          rw [h14] at h₁
          rw [h11] at h₁
          nlinarith
        have hy1 : y = 1 := by
          rw [h14] at h₂
          rw [h11] at h₂
          nlinarith
        simp [hx1, hy1, h14, h11]
      · -- z = -1
        have hx1 : x = -3 := by
          rw [h14] at h₁
          rw [h11] at h₁
          nlinarith
        have hy1 : y = -1 := by
          rw [h14] at h₂
          rw [h11] at h₂
          nlinarith
        simp [hx1, hy1, h14, h11]
  · -- Second direction: finite points → system
    rintro (h | h | h | h)
    · -- First case
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      constructor <;> norm_num
    · -- Second case
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      constructor <;> norm_num
    · -- Third case
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      constructor <;> norm_num
    · -- Fourth case
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      constructor <;> norm_num