import Mathlib

theorem number_theory_85355 (x y z : ℤ) : ¬ √(x^3 + y^3 + z^3) = 1969 := by
  by_contra h
  have h1 : (x^3 + y^3 + z^3 : ℝ) = (1969 : ℝ) ^ 2 := by
    have h2 : √(x^3 + y^3 + z^3) = (1969 : ℝ) := by
      simpa using h
    have h4 : (x^3 + y^3 + z^3 : ℝ) ≥ 0 := by
      by_contra h5
      push_neg at h5
      have h5' : √((x^3 + y^3 + z^3) : ℝ) = 0 := by
        rw [Real.sqrt_eq_zero']
        all_goals nlinarith [h5]
      have h6 : (1969 : ℝ) = (0 : ℝ) := by
        nlinarith [h2, h5']
      nlinarith
    calc
      (x^3 + y^3 + z^3 : ℝ) = (√(x^3 + y^3 + z^3) : ℝ) ^ 2 := by
        rw [Real.sq_sqrt]
        all_goals nlinarith [h4]
      _ = (1969 : ℝ) ^ 2 := by 
        rw [h2]
  have h2' : x^3 + y^3 + z^3 = 1969^2 := by
    norm_cast at h1 ⊢
  have h3 : x^3 + y^3 + z^3 = 3876961 := by
    nlinarith [h2']
  have h4 : (x^3 : ℤ) % 9 = 0 ∨ (x^3 : ℤ) % 9 = 1 ∨ (x^3 : ℤ) % 9 = 8 := by 
    have h1 : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by 
      omega 
    rcases h1 with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
  have h5 : (y^3 : ℤ) % 9 = 0 ∨ (y^3 : ℤ) % 9 = 1 ∨ (y^3 : ℤ) % 9 = 8 := by 
    have h1 : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by 
      omega 
    rcases h1 with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
  have h6 : (z^3 : ℤ) % 9 = 0 ∨ (z^3 : ℤ) % 9 = 1 ∨ (z^3 : ℤ) % 9 = 8 := by 
    have h1 : z % 9 = 0 ∨ z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 3 ∨ z % 9 = 4 ∨ z % 9 = 5 ∨ z % 9 = 6 ∨ z % 9 = 7 ∨ z % 9 = 8 := by 
      omega 
    rcases h1 with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
  have h7 : (x^3 + y^3 + z^3 : ℤ) % 9 = 4 := by 
    omega 
  omega