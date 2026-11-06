import Mathlib

theorem algebra_248480 (x : ℂ) : (x - 1) * (x - 2) * (x - 4) * (x - 5) = 40 ↔
    x = 0 ∨ x = 6 ∨ x = 3 + 2 * Complex.I ∨ x = 3 - 2 * Complex.I := by

  constructor
  · -- Forward direction: if (x-1)(x-2)(x-4)(x-5) = 40, then x is a root
    intro h
    have h1 : (x - 1) * (x - 2) * (x - 4) * (x - 5) - 40 = 0 := by 
      rw [h]
      all_goals ring_nf
    have h2 : (x - 0) * (x - 6) * (x - (3 + 2 * Complex.I)) * (x - (3 - 2 * Complex.I)) = 0 := by
      have h3 : (x - 0) * (x - 6) * (x - (3 + 2 * Complex.I)) * (x - (3 - 2 * Complex.I)) =
          (x^2 - 6 * x) * (x^2 - 6 * x + 13) := by
        simp [pow_two, Complex.ext_iff, Complex.I_mul_I]
        ring_nf
        <;> norm_num
      rw [h3] 
      have h4 : (x ^ 2 - 6 * x) * (x ^ 2 - 6 * x + 13) = (x - 1) * (x - 2) * (x - 4) * (x - 5) - 40 := by
        ring_nf
      rw [h4] at *
      all_goals try exact h1
    cases' (mul_eq_zero.mp h2) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    cases' (mul_eq_zero.mp h5) with h7 h8
    · -- Case x - 0 = 0
      left
      exact eq_of_sub_eq_zero h7
    · -- Case x - 6 = 0
      right
      left
      exact eq_of_sub_eq_zero h8
    · -- Case x - (3 + 2 * i) = 0
      right
      right
      left
      exact eq_of_sub_eq_zero h6
    · -- Case x - (3 - 2 * I) = 0
      right
      right
      right
      exact eq_of_sub_eq_zero h4
  · -- Backward direction: if x is a root, then (x-1)(x-2)(x-4)(x-5) = 40
    rintro (h | h | h | h)
    · -- x = 0
      rw [h]
      norm_num [pow_two, Complex.ext_iff]
    · -- x = 6
      rw [h]
      norm_num [pow_two, Complex.ext_iff]
    · -- x = 3 + 2 * i
      rw [h]
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      all_goals norm_num
    · -- x = 3 - 2 * i
      rw [h]
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      all_goals norm_num