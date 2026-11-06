import Mathlib

/- 4. The numbers $x$ and $y$ are such that the equalities $\operatorname{ctg} x+\operatorname{ctg} y=3$ and $2 \sin (2 x+2 y)=\sin 2 x \sin 2 y$ hold. Find $\operatorname{ctg} x \operatorname{ctg} y$. -/
theorem algebra_156849 {x y : ℝ} (hx : Real.tan x ≠ 0) (hy : Real.tan y ≠ 0)
    (h1 : 1 / Real.tan x + 1 / Real.tan y = 3) (h2 : 2 * Real.sin (2 * x + 2 * y) = Real.sin (2 * x) * Real.sin (2 * y)) :
    1 / Real.tan x * 1 / Real.tan y = 3 / 2 := by
  -- simplify the requirements
  rw [Real.tan_eq_sin_div_cos] at hx hy h1
  simp at hx hy
  -- simplify the first equation
  rw [Real.tan_eq_sin_div_cos] at h1; simp at h1
  apply congr_arg (fun t => t * Real.sin x * Real.sin y) at h1
  rw [add_mul, add_mul, show Real.cos x / Real.sin x * Real.sin x * Real.sin y + Real.cos y / Real.sin y * Real.sin x * Real.sin y = (Real.sin x / Real.sin x) * Real.cos x * Real.sin y + (Real.sin y / Real.sin y) * Real.sin x * Real.cos y by ring_nf, div_self (by exact hx.left), one_mul, div_self (by exact hy.left), one_mul, add_comm, ← Real.sin_add] at h1
  -- simplify the second equation
  rw [Real.sin_two_mul, Real.sin_two_mul, ← mul_add, Real.sin_two_mul] at h2; ring_nf at h2; simp at h2
  -- substite from h1
  rw [h1] at h2
  obtain ⟨hxs, hxc⟩ := hx
  obtain ⟨hys, hyc⟩ := hy
  have h3:3* Real.cos (x + y) = Real.cos x * Real.cos y := by
    apply congr_arg (fun t => t/(Real.sin x * Real.sin y)) at h2
    calc 3 * Real.cos (x + y)
    _ = 3 * Real.cos (x + y) * (Real.sin x / Real.sin x) * (Real.sin y / Real.sin y) := by rw [div_self (by assumption), div_self (by assumption)]; ring_nf
    _ = 3 * Real.sin x * Real.sin y * Real.cos (x + y) / (Real.sin x * Real.sin y) := by ring_nf
    _ = Real.sin x * Real.cos x * Real.sin y * Real.cos y / (Real.sin x * Real.sin y) := by rw [h2]
    _ = (Real.sin x / Real.sin x) * Real.cos x * (Real.sin y / Real.sin y) * Real.cos y := by ring_nf
    _ = Real.cos x * Real.cos y := by rw [div_self (by assumption), div_self (by assumption)]; ring_nf
  rw [Real.cos_add, mul_sub] at h3
  have h4: 2*(Real.cos x)*(Real.cos y) = 3*(Real.sin x)*(Real.sin y) := by linarith
  -- trivial now
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]; ring_nf; simp
  calc (Real.sin x)⁻¹ * Real.cos x * (Real.sin y)⁻¹ * Real.cos y
  _ = 2*Real.cos x * Real.cos y /(2 * Real.sin x * Real.sin y) := by ring_nf
  _ = 3 * Real.sin x * Real.sin y / (2 * Real.sin x * Real.sin y) := by rw [h4]
  _ = 3 / 2 * (Real.sin x / Real.sin x) * (Real.sin y / Real.sin y) := by ring_nf
  _ = 3 / 2 := by rw [div_self (by assumption), div_self (by assumption)]; ring_nf