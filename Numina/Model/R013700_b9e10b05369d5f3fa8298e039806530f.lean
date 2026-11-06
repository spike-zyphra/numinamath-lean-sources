import Mathlib

theorem algebra_171430 (a : ℝ) (z1 z2 z3 : ℂ)
    (hz1 : z1 = a + .I) (hz2 : z2 = 2 * a + 2 * .I)
    (hz3 : z3 = 3 * a + 4 * .I)
    (hge : ∃ r, ‖z2‖ = r * ‖z1‖ ∧ ‖z3‖ = r * ‖z2‖) :
    a = 0 := by
  rcases hge with ⟨r, h1, h2⟩
  have hz1' : ‖z1‖ = Real.sqrt (a ^ 2 + 1) := by
    rw [hz1]
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
  have hz2' : ‖z2‖ = Real.sqrt (4 * a^2 + 4) := by
    rw [hz2]
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
  have hz2'' : ‖z2‖ = 2 * Real.sqrt (a ^ 2 + 1) := by
    rw [hz2']
    have h : Real.sqrt (4 * a^2 + 4) = 2 * Real.sqrt (a ^ 2 + 1) := by
      have h1 : (4 * a^2 + 4 : ℝ) = (2 : ℝ) ^ 2 * (a^2 + 1) := by
        ring_nf
      rw [h1]
      have h2 : Real.sqrt ((2 : ℝ) ^ 2 * (a ^ 2 + 1)) = (2 : ℝ) * Real.sqrt (a ^ 2 + 1) := by
        rw [Real.sqrt_mul (by positivity)]
        rw [Real.sqrt_sq (by norm_num)]
      rw [h2]
    rw [h]
  have hz3' : ‖z3‖ = Real.sqrt (9 * a ^ 2 + 16) := by
    rw [hz3]
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [hz1'] at h1
  rw [hz2''] at h1 h2
  rw [hz3'] at h2
  have hsqrt_pos : Real.sqrt (a ^ 2 + 1) > 0 := by
    have h1 : a ^ 2 + 1 > 0 := by
      have h2 : a ^ 2 ≥ 0 := sq_nonneg a
      linarith
    apply Real.sqrt_pos.mpr
    linarith
  have h5 : r = 2 := by
    have h_eq : 2 * Real.sqrt (a ^ 2 + 1) = r * Real.sqrt (a ^ 2 + 1) := by
      linarith [h1]
    have hsqrt_pos' : Real.sqrt (a ^ 2 + 1) > 0 := hsqrt_pos
    have : r = 2 := by
      apply (mul_right_inj' (ne_of_gt hsqrt_pos')).mp
      linarith [h_eq]
    exact this
  rw [h5] at h2
  have h3 : (Real.sqrt (9 * a ^ 2 + 16) : ℝ) > 0 := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg a, sq_nonneg (3 * a)]
  have h7 : Real.sqrt (a ^ 2 + 1) > 0 := hsqrt_pos
  have eq4 : (Real.sqrt (9 * a ^ 2 + 16) ) ^ 2 = (4 * Real.sqrt (a ^ 2 + 1) ) ^ 2 := by 
    nlinarith [h2]
  have h8 : (Real.sqrt (9 * a ^ 2 + 16) ) ^ 2 = 9 * a ^ 2 + 16 := by
    rw [Real.sq_sqrt]
    nlinarith [sq_nonneg a, sq_nonneg (3 * a)]
  have h9 : (4 * Real.sqrt (a ^ 2 + 1) ) ^ 2 = 16 * (a^2 + 1) := by 
    calc
      (4 * Real.sqrt (a ^ 2 + 1) ) ^ 2 = (16 : ℝ) * (Real.sqrt (a ^ 2 + 1) ) ^ 2 := by 
        ring_nf
      _ = (16 : ℝ) * (a^2 + 1) := by
        rw [Real.sq_sqrt (by nlinarith [sq_nonneg a, sq_nonneg (a^2 + 1)])]
      _ = (16 * (a^2 + 1) ) := by 
        ring
  rw [h8, h9] at eq4
  have h10 : 7 * a ^ 2 = 0 := by
    nlinarith
  have h11 : a ^ 2 = 0 := by
    nlinarith
  have h12 : a = 0 := by
    nlinarith
  exact h12