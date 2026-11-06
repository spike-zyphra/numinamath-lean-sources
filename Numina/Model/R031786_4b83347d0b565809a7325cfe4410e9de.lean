import Mathlib

theorem calculus_14142 :
    IsLeast {n : ℕ | n > 0 ∧ ∀ z : ℂ, z ^ 4 - z ^ 2 + 1 = 0 → z ^ n = 1} 12 := by
  constructor
  · -- Show that 12 is in the set
    constructor
    · norm_num
    · -- Show that ∀ z : ℂ, z ^ 4 - z ^ 2 + 1 = 0 → z ^ 12 = 1
      intro z h
      have h1 : z ^ 4 = z ^ 2 - 1 := by
        have h2 : z ^ 4 - z ^ 2 + 1 = 0 := h
        calc
          z ^ 4 = (z ^ 4 - z ^ 2 + 1) + z ^ 2 - 1 := by ring
          _ = 0 + z ^ 2 - 1 := by rw [h2]
          _ = z ^ 2 - 1 := by ring
      have h2 : z ^ 8 = -z ^ 2 := by
        calc
          z ^ 8 = (z ^ 4) ^ 2 := by ring
          _ = (z ^ 2 - 1) ^ 2 := by rw [h1]
          _ = z ^ 4 - 2 * z ^ 2 + 1 := by ring
          _ = (z ^ 2 - 1) - 2 * z ^ 2 + 1 := by rw [h1]
          _ = -z ^ 2 := by ring_nf
      have h3 : z ^ 12 = 1 := by
        calc
          z ^ 12 = z ^ 8 * z ^ 4 := by ring
          _ = (-z ^ 2) * (z ^ 2 - 1) := by rw [h2, h1]
          _ = -z ^ 4 + z ^ 2 := by ring
          _ = -(z ^ 2 - 1) + z ^ 2 := by rw [h1]
          _ = 1 := by ring_nf
      exact_mod_cast h3
  · -- Show that 12 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_uni⟩
    by_contra h
    push_neg at h
    have h1 := hn_uni (Complex.exp (Complex.I * Real.pi / 6)) (by
      simp [pow_two, pow_succ, Complex.ext_iff, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im, mul_add, mul_comm, mul_assoc]
      field_simp [Real.sin_sq]
      <;> ring_nf <;> field_simp [Real.sin_sq]
      <;> linarith [Real.sin_pos_of_pos_of_lt_pi (show (0 : ℝ) < Real.pi / 6 by linarith [Real.pi_pos] ), Real.pi_pos]
    )
    have h2 : (Complex.exp (Complex.I * Real.pi / 6) ) ^ n = 1 := h1
    have h3 : (Complex.exp (Complex.I * Real.pi / 6) ) ^ n = Complex.exp (Complex.I * Real.pi / 6 * ↑n) := by
      rw [← Complex.exp_nat_mul]
      ring_nf
    rw [h3] at h2
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h2
    have h4 : Real.pi * (n : ℝ) / 6 = 2 * Real.pi * (↑k : ℝ) := by
      simp [Complex.ext_iff] at hk
      linarith
    have h5 : (n : ℝ) = 12 * (k : ℝ) := by
      nlinarith [Real.pi_pos, Real.pi_gt_three]
    have h6 : n = 12 * k := by
      exact_mod_cast h5
    omega