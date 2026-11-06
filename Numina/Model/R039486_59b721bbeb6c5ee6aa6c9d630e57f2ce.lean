import Mathlib

theorem number_theory_32927 : {(x, y, z) : ℕ × ℕ × ℕ | x > y ∧ y > z ∧ z > 0 ∧ (1 : ℚ) / x + 2 / y + 3 / z = 1} = {(36, 9, 4), (20, 10, 4), (15, 6, 5)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- First direction: proving that if (x, y, z) satisfies the conditions, then it's in the set.
    rintro ⟨h₁, h₂, h₃, heq⟩
    have h4 : x > 0 := by linarith
    have h5 : y > 0 := by linarith
    have h6 : z > 0 := h₃
    have eq1 : (↑x : ℚ)⁻¹ + 2 / (↑y : ℚ) + 3 / (↑z : ℚ) = 1 := by
      simpa using heq
    have eq2 : (y : ℚ) * (z : ℚ) + 2 * (x : ℚ) * (z : ℚ) + 3 * (x : ℚ) * (y : ℚ) = (x : ℚ) * (y : ℚ) * (z : ℚ) := by
      have h7 : x > 0 := h4
      have h8 : y > 0 := h5
      have h9 : z > 0 := h6
      have h10 : (↑x : ℚ) > 0 := by positivity
      have h11 : (↑y : ℚ) > 0 := by positivity
      have h12 : (↑z : ℚ) > 0 := by positivity
      field_simp at eq1 ⊢
      nlinarith [mul_pos (show (0 : ℚ) < ↑x by positivity) (show (0 : ℚ) < ↑y by positivity), 
                mul_pos (show (0 : ℚ) < ↑y by positivity) (show (0 : ℚ) < ↑z by positivity), 
                mul_pos (show (0 : ℚ) < ↑x by positivity) (show (0 : ℚ) < ↑z by positivity)]
    have eq3 : (y : ℕ) * (z : ℕ) + 2 * (x : ℕ) * (z : ℕ) + 3 * (x : ℕ) * (y : ℕ) = (x : ℕ) * (y : ℕ) * (z : ℕ) := by
      exact_mod_cast eq2
    -- Now, we need to find upper bounds on z.
    have eq4 : z ≤ 16 := by
      nlinarith [mul_pos (show 0 < (x : ℕ) by linarith) (show 0 < (y : ℕ) by linarith), 
                  mul_pos (show 0 < (y : ℕ) by linarith) (show 0 < (z : ℕ) by linarith), 
                  mul_pos (show 0 < (x : ℕ) by linarith) (show 0 < (z : ℕ) by linarith), 
                  mul_pos (show 0 < (y : ℕ) by linarith) (show 0 < (z : ℕ) by linarith), 
                  sq_nonneg (x - y : ℤ), sq_nonneg (y - z : ℤ), sq_nonneg (x - y : ℤ), sq_nonneg (y - 10 : ℤ), sq_nonneg (z - 4 : ℤ)]
    interval_cases z <;> try { 
      omega
    } <;> try { 
      have eq5 : y ≤ 32 := by
        nlinarith [sq_nonneg (y - 10 : ℤ), sq_nonneg (x - 15 : ℤ), sq_nonneg (y - 16 : ℤ), sq_nonneg (x - 20 : ℤ), sq_nonneg (y - 10 : ℤ), sq_nonneg (x - 36 : ℤ)]
      interval_cases y <;> omega
    }
  · -- Show that the set {(36, 9, 4), (20, 10, 4), (15, 6, 5)} is contained in the set of solutions.
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num