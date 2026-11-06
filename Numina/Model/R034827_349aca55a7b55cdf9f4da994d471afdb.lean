import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_12476 {a : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ)
  (hf : f = λ x => a * sin x - 1 / 2 * cos (2 * x) + a - 3 / a + 1 / 2)
  (h : ∀ x, f x ≤ 0) :
  0 < a ∧ a ≤ 1 := by

  have h1 : f (Real.pi / 2) ≤ 0 := h (Real.pi / 2)
  have h1' : f (Real.pi / 2) = 2 * a + 1 - 3 / a := by 
    rw [hf]
    have hsin : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have hcos : cos (2 * (Real.pi / 2)) = -1 := by 
      have h1 : 2 * (Real.pi / 2) = Real.pi := by ring
      rw [h1]
      norm_num
    simp [hsin, hcos]
    field_simp [ha]
    ring
  rw [h1'] at h1
  
  have h2 : f (- (Real.pi / 2)) ≤ 0 := h (- (Real.pi / 2))
  have h2' : f (- (Real.pi / 2)) = 1 - 3 / a := by 
    rw [hf]
    have hsin : sin (- (Real.pi / 2)) = -1 := by 
      have : sin (- (Real.pi / 2)) = -sin (Real.pi / 2) := by rw [sin_neg]
      rw [this, Real.sin_pi_div_two]
    have hcos : cos (2 * (- (Real.pi / 2))) = -1 := by 
      have h1 : 2 * (- (Real.pi / 2)) = - (Real.pi) := by ring
      rw [h1]
      norm_num
      <;> ring_nf <;> norm_num
    simp [hsin, hcos]
    field_simp [ha]
    ring
  rw [h2'] at h2
  
  have h3 : 0 < a := by
    by_contra h3
    push_neg at h3
    by_cases h4 : a < 0
    · -- Assume a < 0
      have h5 : 1 - 3 / a ≤ 0 := by linarith [h2]
      have h6 : (1 : ℝ) ≤ 3 / a := by linarith [h5]
      have h7 : a * (1 : ℝ) ≥ a * (3 / a) := by 
        apply mul_le_mul_of_nonpos_left
        linarith
        linarith
      have h8 : a * (3 / a) = 3 := by 
        field_simp [ha]
      have h9 : a * (1 : ℝ) ≥ 3 := by linarith [h7, h8]
      nlinarith
    · -- Assume a ≥ 0
      have h4' : a ≥ 0 := by linarith
      have h4'' : a = 0 := by linarith
      contradiction
  
  -- From h1: 2a + 1 - 3/a ≤ 0 and h3: 0 < a ⇒ a ≤ 1
  have h4 : a ≤ 1 := by
    have h5 : 2 * a + 1 - 3 / a ≤ 0 := by linarith [h1]
    have h6 : 2 * a ^ 2 + a - 3 ≤ 0 := by
      have h7 : a > 0 := h3
      have h8 : 2 * a + 1 - 3 / a ≤ 0 := by linarith [h1]
      have h9 : a > 0 := h3
      have h10 : (2 * a ^ 2 + a - 3) / a ≤ 0 := by
        have h11 : (2 * a ^ 2 + a - 3) / a = 2 * a + 1 - 3 / a := by
          field_simp [h9]
          <;> ring
        linarith [h11, h8]
      have h11 : 2 * a ^ 2 + a - 3 ≤ 0 := by
        by_contra h11
        push_neg at h11
        have h2' : (2 * a ^ 2 + a - 3) / a > 0 := by
          apply div_pos
          linarith
          linarith
        linarith
      linarith
    nlinarith [h3]

  exact ⟨h3, h4⟩