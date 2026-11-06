import Mathlib
import Mathlib.Analysis.InnerProductSpace.Basic

open Real

theorem inequalities_601397 (x : ℝ) (hx : 3 / 2 ≤ x ∧ x ≤ 5) :
    2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x) < 2 * Real.sqrt 19 := by

  generalize hv₁: !₂[(1:ℝ), 1, 1, 1] = v₁
  generalize hv₂: !₂[sqrt (x + 1), sqrt (x + 1), sqrt (2 * x - 3), sqrt (15 - 3 * x)] = v₂
  have h_lt_if := (inner_lt_norm_mul_iff_real (x := v₁) (y := v₂)).mpr
  have h₁: x + 1 ≥ 0 := by bound
  have h₂: 2 * x - 3 ≥ 0 := by bound
  have h₃: 15 - 3 * x ≥ 0 := by bound
  simp [<-hv₁, <-hv₂, PiLp.norm_eq_of_L2, Fin.sum_univ_four] at h_lt_if
  simp [Real.sq_sqrt h₁, Real.sq_sqrt h₂, Real.sq_sqrt h₃] at h_lt_if
  ring_nf at h_lt_if
  have h_sqrt_4: √4 = 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by linarith) (by linarith)]
    norm_num
  conv at h_lt_if => rhs; rhs; rw [h_sqrt_4, mul_comm]
  ring_nf
  have h₅ (a: ℝ) {b c: ℝ}: 0 ≤ a → 0 ≤ b → √a = c * √b → a = c^2 * b := by
    intro ha hb hc
    convert congr_arg (λx => x^2) hc
    · field_simp
    · ring_nf
      simp [add_comm, Real.sq_sqrt hb]
  apply lt_of_lt_of_le (b := √(14 +x) * 2)
  · apply h_lt_if
    intro H
    have h_v_0: √(14 + x) = 2*√(x+1) := by convert congr_fun H 0 <;> simp [h_sqrt_4]; ring_nf
    have h_v_2: √(14 + x) = 2*√(2*x - 3) := by convert congr_fun H 2 <;> simp [h_sqrt_4]; ring_nf
    have h_v_0_sq: 14 + x = 4 * (x + 1) := by convert h₅ (14 + x) (by bound) h₁ h_v_0; linarith
    have h_v_2_sq: 14 + x = 4 * (2*x - 3) := by convert h₅ (14 + x) (by bound) h₂ h_v_2; linarith
    have h_x₁ : x = 13 / 3 := by linarith
    simp [h_x₁] at h_v_2_sq
    linarith
  · ring_nf
    simp
    bound
