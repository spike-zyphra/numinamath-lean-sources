import Mathlib

theorem number_theory_295813 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≤ y) (hyz : y ≤ z) :
    (1 / x : ℚ) + (1 / y : ℚ) + (1 / z : ℚ) = 1 ↔
    (x = 3 ∧ y = 3 ∧ z = 3) ∨ (x = 2 ∧ y = 4 ∧ z = 4) ∨ (x = 2 ∧ y = 3 ∧ z = 6) := by 
  constructor
  · -- Forward direction: equation implies the solutions
    intro h
    have h1 : (x : ℚ) > 0 := by exact_mod_cast hx
    have h2 : (y : ℚ) > 0 := by exact_mod_cast hy
    have h3 : (z : ℚ) > 0 := by exact_mod_cast hz
    have h4 : (x : ℚ) ≤ (y : ℚ) := by exact_mod_cast hxy
    have h5 : (y : ℚ) ≤ (z : ℚ) := by exact_mod_cast hyz
    have h_eq : (x : ℚ) * (y : ℚ) * (z : ℚ) = (x : ℚ) * (y : ℚ) + (x : ℚ) * (z : ℚ) + (y : ℚ) * (z : ℚ) := by 
      field_simp at h ⊢
      nlinarith
    have h_eq_nat : (x : ℕ) * (y : ℕ) * (z : ℕ) = (x : ℕ) * (y : ℕ) + (x : ℕ) * (z : ℕ) + (y : ℕ) * (z : ℕ) := by 
      exact_mod_cast h_eq
    have h2 : x ≤ 3 := by
      by_contra h 
      push_neg at h 
      have h3 : x ≥ 4 := by omega 
      have h4 : y ≥ 4 := by 
        nlinarith [hxy, h3] 
      have h5 : z ≥ 4 := by 
        nlinarith [hyz, h4]
      -- Now using these bounds to show the original equation is false 
      have h7 : (x : ℚ) ≥ 4 := by 
        exact_mod_cast h3 
      have h8 : (y : ℚ) ≥ 4 := by 
        exact_mod_cast h4 
      have h9 : (z : ℚ) ≥ 4 := by 
        exact_mod_cast h5 
      -- The key insight: if x,y,z >= 4, then their reciprocals are too small 
      have h10 : (1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) : ℚ) < (1 : ℚ) := by
        have h10a : (1 / (x : ℚ) : ℚ) ≤ (1 / (4 : ℚ) : ℚ) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr 
          nlinarith 
        have h10b : (1 / (y : ℚ) : ℚ) ≤ (1 / (4 : ℚ) : ℚ) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr 
          nlinarith 
        have h10c : (1 / (z : ℚ) : ℚ) ≤ (1 / (4 : ℚ) : ℚ) := by 
          apply (div_le_div_iff (by positivity) (by positivity)).mpr 
          nlinarith 
        have h11 : (1 / (4 : ℚ) : ℚ) = (1 / 4 : ℚ) := by rfl 
        have h12 : (1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) : ℚ) ≤ (3 / 4 : ℚ) := by
          linarith [h10a, h10b, h10c, h11] 
        nlinarith 
      linarith [h, h10]
    have h2 : x ≤ 3 := h2 
    have h4 : x = 1 ∨ x = 2 ∨ x = 3 := by omega 
    rcases h4 with (hx1 | hx2 | hx3)
    · -- Assume x = 1 
      rw [hx1] at h_eq_nat 
      nlinarith [sq_nonneg (y : ℕ), sq_nonneg (z : ℕ), mul_pos (show 0 < y by linarith) (show 0 < z by linarith)]
    · -- Assume x = 2 
      rw [hx2] at h_eq_nat 
      have h5 : y ≤ 6 := by 
        nlinarith [h_eq_nat, mul_pos (show 0 < 2 by norm_num) (show 0 < y by linarith), mul_pos (show 0 < 2 by norm_num) (show 0 < z by linarith), mul_pos (show 0 < y by linarith) (show 0 < z by linarith), sq_nonneg (y : ℕ), sq_nonneg (z : ℕ), hxy, hyz]
      interval_cases y <;> try { 
        omega 
      } 
    · -- Assume x = 3 
      rw [hx3] at h_eq_nat 
      have h5 : y ≤ 6 := by
        nlinarith [h_eq_nat, mul_pos (show 0 < 3 by norm_num) (show 0 < y by linarith), mul_pos (show 0 < 3 by norm_num) (show 0 < z by linarith), mul_pos (show 0 < y by linarith) (show 0 < z by linarith), sq_nonneg (y : ℕ), sq_nonneg (z : ℕ), hxy, hyz]
      interval_cases y <;> try { 
        omega 
      }
  · -- Backward direction: solutions satisfy the equation
    rintro (h | h | h)
    · -- (3, 3, 3)
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num 
    · -- (2, 4, 4)
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num 
    · -- (2, 3, 6)
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num