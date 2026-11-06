import Mathlib

theorem algebra_317019 (a : ℝ) (z1 z2 z3 : ℂ)
    (hz1 : z1 = a + .I) (hz2 : z2 = 2 * a + 2 * .I) (hz3 : z3 = 3 * a + 4 * .I)
    (hge : ∃ r, ‖z1‖ = r * ‖z2‖ ∧ ‖z2‖ = r * ‖z3‖) :
    a = 0 := by
  rcases hge with ⟨r, h1, h2⟩
  have hz1' : ‖z1‖ = Real.sqrt (a^2 + 1) := by
    rw [hz1]
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num
    <;> ring
  have hz2' : ‖z2‖ = Real.sqrt (4*a^2 + 4) := by
    rw [hz2]
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num
    <;> ring
  have hz3' : ‖z3‖ = Real.sqrt (9*a^2 + 16) := by
    rw [hz3]
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num
    <;> ring
  rw [hz1', hz2'] at h1
  rw [hz2', hz3'] at h2
  have eq1 : Real.sqrt (a^2 + 1) = r * Real.sqrt (4*a^2 + 4) := by
    linarith
  have eq2 : Real.sqrt (4*a^2 + 4) = r * Real.sqrt (9*a^2 + 16) := by
    linarith
  have h1' : a^2 + 1 = r^2 * (4*a^2 + 4) := by
    calc
      a^2 + 1 = (Real.sqrt (a^2 + 1)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (r * Real.sqrt (4*a^2 + 4)) ^ 2 := by rw [eq1]
      _ = r^2 * (Real.sqrt (4*a^2 + 4)) ^ 2 := by ring
      _ = r^2 * (4*a^2 + 4) := by
        rw [Real.sq_sqrt]
        positivity
  have h2' : 4*a^2 + 4 = r^2 * (9*a^2 + 16) := by
    calc
      4*a^2 + 4 = (Real.sqrt (4*a^2 + 4)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (r * Real.sqrt (9*a^2 + 16)) ^ 2 := by rw [eq2]
      _ = r^2 * (Real.sqrt (9*a^2 + 16)) ^ 2 := by ring
      _ = r^2 * (9*a^2 + 16) := by
        rw [Real.sq_sqrt]
        positivity
  have eq3 : r^2 = (a^2 + 1) / (4*a^2 + 4) := by
    have hne : 4*a^2 + 4 ≠ 0 := by
      nlinarith
    field_simp [hne]
    nlinarith
  rw [eq3] at h2'
  have h5 : (4*a^2 + 4)^2 = (a^2 + 1) * (9*a^2 + 16) := by
    field_simp [(show 4*a^2 + 4 ≠ 0 by nlinarith)] at h2' ⊢
    nlinarith
  have h6 : 7*a^4 + 7*a^2 = 0 := by
    nlinarith [h5]
  have h8 : a^2 = 0 := by
    nlinarith [sq_nonneg (a^2), sq_nonneg a]
  have h9 : a = 0 := by
    nlinarith
  exact h9