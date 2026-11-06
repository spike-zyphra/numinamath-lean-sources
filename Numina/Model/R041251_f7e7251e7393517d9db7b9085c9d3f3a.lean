import Mathlib

open Complex

theorem algebra_13418 :
  {x : ℂ | (x^3 + 3 * x^2 * √2 + 6 * x + 2 * √2) + (x + √2) = 0} = {-↑√2, -√2 + I, -√2 - I} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Forward direction: if x is a solution, then x ∈ {-√2, -√2 + I, -√2 - I}
    intro h
    have eq1 : x^3 + 3 * x^2 * √2 + 6 * x + 2 * √2 + (x + √2) = 0 := by
      have h1 : (x^3 + 3 * x^2 * √2 + 6 * x + 2 * √2) + (x + √2) = 0 := h
      simpa using h1
    have eq2 : (x + ↑√2) ^ 3 + (x + ↑√2) = 0 := by
      simp [pow_three, Complex.ext_iff, mul_add, add_mul, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, mul_comm] at *
      ring_nf at eq1 ⊢
      norm_num [Real.sqrt_mul_self] at eq1 ⊢
      constructor <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have eq3 : (x + ↑√2) * ((x + ↑√2) ^ 2 + 1) = 0 := by
      have h2 : (x + ↑√2) ^ 3 + (x + ↑√2) = 0 := eq2
      calc
        (x + ↑√2) * ((x + ↑√2) ^ 2 + 1) = (x + ↑√2) ^ 3 + (x + ↑√2) := by ring
        _ = 0 := h2
    cases' (mul_eq_zero.mp eq3) with h4 h5
    · -- When (x + ↑√2) = 0
      have h7 : x + ↑√2 = 0 := h4
      have h8 : x = -↑√2 := by
        calc
          x = (x + ↑√2) - ↑√2 := by ring
          _ = -↑√2 := by rw [h7]; ring
      simp [h8]
    · -- When (x + ↑√2) ^ 2 + 1 = 0
      have h6 : (x + ↑√2) ^ 2 + 1 = 0 := h5
      have h8 : (x + ↑√2) = Complex.I ∨ (x + ↑√2) = -Complex.I := by
        have h9 : (x + ↑√2) ^ 2 + 1 = 0 := h6
        have eq1 : (x + ↑√2) ^ 2 + 1 = (x + ↑√2 - Complex.I) * (x + ↑√2 + Complex.I) := by
          ring_nf
          simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
          all_goals ring
        rw [eq1] at h9
        cases' (mul_eq_zero.mp h9) with h10 h11
        · -- (x + ↑√2 - Complex.I) = 0
          left
          have h12 : x + ↑√2 = Complex.I := by
            have h13 : x + ↑√2 - Complex.I = 0 := h10
            calc
              x + ↑√2 = (x + ↑√2 - Complex.I) + Complex.I := by ring
              _ = Complex.I := by rw [h13]; ring
          exact h12
        · -- (x + ↑√2 + Complex.I) = 0
          right
          have h14 : x + ↑√2 = -Complex.I := by
            have h15 : x + ↑√2 + Complex.I = 0 := h11
            calc
              x + ↑√2 = (x + ↑√2 + Complex.I) - Complex.I := by ring
              _ = -Complex.I := by rw [h15]; ring
          exact h14
      cases h8 with
      | inl h9 =>
        have h10 : x = -↑√2 + Complex.I := by
          calc
            x = (x + ↑√2) - ↑√2 := by ring
            _ = -↑√2 + Complex.I := by rw [h9]; all_goals ring
        simp [h10]
      | inr h9 =>
        have h10 : x = -↑√2 - Complex.I := by
          calc
            x = (x + ↑√2) - ↑√2 := by ring
            _ = -↑√2 - Complex.I := by rw [h9]; all_goals ring
        simp [h10]
  · -- Backward direction: each element in {-√2, -√2 + I, -√2 - I} is a solution
    rintro (h | h | h)
    · -- When x = -↑√2
      rw [h]
      simp [pow_three, Complex.ext_iff, mul_add, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      all_goals ring_nf <;> norm_num [Real.sqrt_mul_self, mul_add, pow_two]
    · -- When x = -√2 + I
      rw [h]
      simp [pow_three, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, pow_two, mul_add, Complex.I_re, Complex.I_im]
      ring_nf
      norm_num [Real.sqrt_mul_self, pow_two, Complex.I_mul_I, mul_add, pow_three, pow_two]
    · -- When x = -√2 - I
      rw [h]
      simp [pow_three, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, pow_two, mul_add, Complex.I_re, Complex.I_im]
      ring_nf
      norm_num [Real.sqrt_mul_self, pow_two, Complex.I_mul_I, mul_add, pow_three, pow_two]