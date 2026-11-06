import Mathlib

theorem algebra_282712 : 
  {(x, y) : ℂ × ℂ | x^4 + y^4 = 272 ∧ x + y = 6} =
  {(2, 4), (4, 2), (3 + Complex.I * Real.sqrt 55, 3 - Complex.I * Real.sqrt 55), 
   (3 - Complex.I * Real.sqrt 55, 3 + Complex.I * Real.sqrt 55)} := by
  ext ⟨x, y⟩
  simp [-one_div]
  constructor
  · -- Assume (x, y) satisfies the system, prove it's one of the four solutions
    rintro ⟨h₁, h₂⟩
    have h3 : y = 6 - x := by
      calc
        y = (x + y) - x := by ring
        _ = 6 - x := by rw [h₂]
    rw [h3] at h₁
    have h4 : (x - 2) * (x - 4) * (x ^ 2 - 6 * x + 64) = 0 := by
      ring_nf at h₁ ⊢
      norm_num [Complex.ext_iff, pow_two, pow_three, pow_succ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h₁ ⊢
      constructor <;> 
        nlinarith [Real.sqrt_nonneg 55, Real.sq_sqrt (show (0 : ℝ) ≤ 55 by norm_num)]
    cases' (mul_eq_zero.mp h4) with h5 h6
    cases' (mul_eq_zero.mp h5) with h7 h8
    · 
      have hx : x = 2 := by 
        have h9 : x - 2 = 0 := h7
        calc
          x = (x - 2) + 2 := by ring
          _ = 0 + 2 := by rw [h9]
          _ = 2 := by ring
      have hy : y = 4 := by 
        rw [hx] at h3
        calc
          y = 6 - (2 : ℂ) := by rw [h3]
          _ = 4 := by ring
      simp [hx, hy]
    · 
      have hx : x = 4 := by 
        have h9 : x - 4 = 0 := h8
        calc
          x = (x - 4) + 4 := by ring
          _ = 0 + 4 := by rw [h9]
          _ = 4 := by ring
      have hy : y = 2 := by 
        rw [hx] at h3
        calc
          y = 6 - (4 : ℂ) := by rw [h3]
          _ = 2 := by ring
      simp [hx, hy]
    · 
      have h9 : x ^ 2 - 6 * x + 64 = 0 := h6
      have h11 : x = 3 + Complex.I * Real.sqrt 55 ∨ x = 3 - Complex.I * Real.sqrt 55 := by
        have h12 : x ^ 2 - 6 * x + 64 = 0 := h9
        have h13 : x ^ 2 - 6 * x + 64 = (x - (3 + Complex.I * Real.sqrt 55)) * (x - (3 - Complex.I * Real.sqrt 55)) := by
          ring_nf
          simp [Complex.ext_iff, pow_two, mul_add, mul_sub, Complex.I_mul_I, mul_assoc]
          ring_nf
          <;> norm_num [Real.sqrt_mul_self]
          all_goals ring
        rw [h13] at h12
        cases' mul_eq_zero.1 h12 with h14 h15
        · left
          calc
            x = (x - (3 + Complex.I * Real.sqrt 55)) + (3 + Complex.I * Real.sqrt 55) := by ring
            _ = (3 + Complex.I * Real.sqrt 55) := by rw [h14]; ring
        · right
          calc
            x = (x - (3 - Complex.I * Real.sqrt 55)) + (3 - Complex.I * Real.sqrt 55) := by ring
            _ = (3 - Complex.I * Real.sqrt 55) := by rw [h15]; ring
      cases h11 with
      | inl hx =>
        have hy : y = 3 - Complex.I * Real.sqrt 55 := by
          rw [hx] at h3
          rw [h3]
          ring_nf
        simp [hx, hy]
      | inr hx =>
        have hy : y = 3 + Complex.I * Real.sqrt 55 := by
          rw [hx] at h3
          rw [h3]
          ring_nf
        simp [hx, hy]
  · -- Assume (x, y) is one of the four solutions, prove it satisfies the system
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · constructor
      · norm_num [pow_succ, Complex.ext_iff]
      · norm_num [Complex.ext_iff]
    · constructor
      · norm_num [pow_succ, Complex.ext_iff]
      · norm_num [Complex.ext_iff]
    · constructor
      · simp [pow_two, pow_succ, Complex.ext_iff, mul_add, add_mul, mul_assoc, pow_succ, Complex.I_mul_I, mul_add, mul_assoc, Real.sqrt_mul_self]
        ring_nf
        norm_num
      · norm_num [Complex.ext_iff, pow_succ, Complex.I_mul_I, mul_add, Real.sqrt_mul_self]
    · constructor
      · simp [pow_two, pow_succ, Complex.ext_iff, mul_add, add_mul, mul_assoc, pow_succ, Complex.I_mul_I, mul_add, mul_assoc, Real.sqrt_mul_self]
        ring_nf
        norm_num
      · norm_num [Complex.ext_iff, pow_succ, Complex.I_mul_I, mul_add, Real.sqrt_mul_self]