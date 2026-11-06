import Mathlib

theorem inequalities_47644 (a b : ℤ) (h : ∀ x : ℝ, x ^ 2 + a * x + b ≥ -9 / 10) :
    ∀ x : ℝ, x ^ 2 + a * x + b ≥ -1 / 4 := by 
  intro x
  have h1 := h (- (a : ℝ) / 2)
  have h2 : ( - (a : ℝ) / 2 ) ^ 2 + (a : ℝ) * ( - (a : ℝ) / 2 ) + b = (b : ℝ) - (a ^ 2 : ℝ) / 4 := by
    ring_nf
    <;> field_simp <;> ring
  rw [h2] at h1 
  have h3 : (b : ℝ) - (a ^ 2 : ℝ) / 4 ≥ -9 / 10 := by 
    linarith
  have h4 : (b : ℝ) - (a ^ 2 : ℝ) / 4 ≥ -1 / 4 := by
    by_contra h1
    push_neg at h1
    have h5 : (b : ℝ) - (a ^ 2 : ℝ) / 4 < -1 / 4 := by linarith
    have h6 : (4 * (b : ℝ) : ℝ) - (a ^ 2 : ℝ) < (0 : ℝ) := by
      nlinarith
    have h6' : (4 * (b : ℝ) : ℝ) - (a ^ 2 : ℝ) < (0 : ℝ) := h6
    have h6'': (4 * b : ℤ) - (a ^ 2 : ℤ) < (0 : ℤ) := by
      by_contra h
      push_neg at h
      have : (4 * (b : ℝ) : ℝ) - (a ^ 2 : ℝ) ≥ (0 : ℝ) := by 
        exact_mod_cast h
      nlinarith 
    have h7 : (4 * b : ℤ) - (a ^ 2 : ℤ) ≥ -3 := by
      by_contra h
      push_neg at h
      have h8 : (4 * (b : ℝ) : ℝ) - (a ^ 2 : ℝ) ≤ (-4 : ℝ) := by
        have h8' : (4 * b : ℤ) - (a ^ 2 : ℤ) ≤ -4 := by 
          omega
        exact_mod_cast h8'
      nlinarith [show (a ^ 2 : ℝ) = (a ^ 2 : ℤ) by simp, show (b : ℝ) = (b : ℤ) by simp]
    have h8 : (4 * b : ℤ) - (a ^ 2 : ℤ) ≤ -1 := by
      by_contra h
      push_neg at h 
      have h9 : (4 * (b : ℝ) : ℝ) - (a ^ 2 : ℝ) ≥ (0 : ℝ) := by 
        exact_mod_cast h 
      nlinarith
    have h9 : (4 * b : ℤ) - (a ^ 2 : ℤ) < (0 : ℤ) := by
      omega
    have h10 : (4 * b : ℤ) - (a ^ 2 : ℤ) = -3 ∨ (4 * b : ℤ) - (a ^ 2 : ℤ) = -2 ∨ (4 * b : ℤ) - (a ^ 2 : ℤ) = -1 := by 
      omega
    rcases h10 with (h10 | h10 | h10)
    · -- Case where 4b - a² = -3
      have h11 : a ^ 2 % 4 = 3 := by
        have h12 : (4 * b : ℤ) - (a ^ 2 : ℤ) = -3 := h10
        have h13 : a ^ 2 = 4 * b + 3 := by linarith
        omega
      have h11' : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by 
        omega
      rcases h11' with (h11' | h11' | h11' | h11') <;> simp [pow_two, Int.add_emod, Int.mul_emod, h11'] at h11
    · -- Case where 4b - a² = -2
      have h11 : a ^ 2 % 4 = 2 := by
        have h12 : (4 * b : ℤ) - (a ^ 2 : ℤ) = -2 := h10
        have h13 : a ^ 2 = 4 * b + 2 := by linarith
        omega
      have h11' : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by 
        omega
      rcases h11' with (h11' | h11' | h11' | h11') <;> simp [pow_two, Int.add_emod, Int.mul_emod, h11'] at h11
    · -- Case where 4b - a² = -1
      have h10' : (4 * b : ℤ) - (a ^ 2 : ℤ) = -1 := h10
      have h12 : (b : ℝ) - (a ^ 2 : ℝ) / 4 = -1 / 4 := by
        have h13 : (4 * b : ℤ) - (a ^ 2 : ℤ) = -1 := by 
          omega 
        have h14 : (4 * (b : ℝ) : ℝ) - (a ^ 2 : ℝ) = -1 := by
          exact_mod_cast h13 
        linarith 
      have h13 : (b : ℝ) - (a ^ 2 : ℝ) / 4 < -1 / 4 := by 
        linarith [h1]
      linarith [h13, h12]
  have h50 : (x + (a : ℝ) / 2) ^ 2 ≥ 0 := by 
    apply sq_nonneg 
  nlinarith [sq_nonneg (x + (a : ℝ) / 2), sq_nonneg ((a : ℝ) / 2), sq_nonneg ((a : ℝ) / 2 - (x + (a : ℝ) / 2)), h4, h1]