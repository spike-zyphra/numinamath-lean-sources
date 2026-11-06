import Mathlib

theorem algebra_310141 {s t : ℝ} (h₀ : 19 * s^2 + 99 * s + 1 = 0) (h₁ : t^2 + 99 * t + 19 = 0)
    (h₂ : s * t ≠ 1) : (s * t + 4 * s + 1) / t = -5 := by
  have h3 : s ≠ 0 := by
    by_contra h
    rw [h] at h₀
    nlinarith
  have h4 : t ≠ 0 := by
    by_contra h
    rw [h] at h₁
    nlinarith
  have eq1 : 19 * s + 1 / s = -99 := by
    have h5 : s ≠ 0 := h3
    field_simp
    nlinarith
  have eq2 : t + 19 / t = -99 := by
    have h6 : t ≠ 0 := h4
    field_simp
    nlinarith
  have h7 : 19 * s + 1 / s = t + 19 / t := by 
    linarith [eq1, eq2]
  have h8 : s * t - 1 ≠ 0 := by
    intro h
    apply h₂
    linarith
  have eq3 : 19 * s^2 * t + t - s * t^2 - 19 * s = 0 := by 
    have h6 : s ≠ 0 := h3
    have h7' : t ≠ 0 := h4
    field_simp [h6, h7'] at h7
    nlinarith
  have eq4 : (19 * s - t) * (s * t - 1) = 0 := by 
    nlinarith [eq3]
  cases' (mul_eq_zero.mp eq4) with h9 h10
  · -- either first factor is zero: so 19s - t =0 → t=19s
    have ht : t = 19 * s := by linarith
    have eq8 : s * t + 4 * s + 1 = -95 * s := by
      rw [ht]
      have h10 : 19 * s^2 = -99 * s - 1 := by linarith
      nlinarith [h10]
    have eq9 : (s * t + 4 * s + 1) / t = (-95 * s) / t := by 
      rw [eq8]
    rw [eq9]
    rw [ht]
    have h6 : s ≠ 0 := h3
    field_simp [h6]
    <;> nlinarith
  · -- second factor is zero: s*t -1=0 → s*t=1
    have h11 : s * t = 1 := by linarith
    have h12 : s * t = 1 := h11
    contradiction