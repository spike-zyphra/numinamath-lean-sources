import Mathlib
open Real

/- 【Example 2.1】In $\triangle A B C$, prove:
(1) $\tan n A+\tan n B+\tan n C=\tan n A \tan n B \tan n C, n$ is an integer;
(2) $\cot \frac{n A}{2}+\cot \frac{n B}{2}+\cot \frac{n C}{2}=\cot \frac{n A}{2} \cot \frac{n B}{2} \cot \frac{n C}{2}, n$ is an odd number. -/

lemma lemma_1 {x : ℝ} {k : ℤ} : cot ((2 * k + 1) * π / 2 - x) = tan x := by
  have h_cos : cos ((2 * k + 1) * π / 2) = 0
  · rw [cos_eq_zero_iff]; use k
  have h_sin : sin ((2 * k + 1) * π / 2) ≠ 0
  · rw [sin_ne_zero_iff]
    intro n
    field_simp
    move_mul [π]
    intro h
    rw [mul_right_cancel_iff_of_pos Real.pi_pos] at h
    absurd h
    norm_cast
    omega
  rw [cot_eq_cos_div_sin, sin_sub, cos_sub, h_cos,
      zero_mul, zero_mul, zero_add, sub_zero, mul_div_mul_comm,
      ←tan_eq_sin_div_cos, mul_left_eq_self₀]
  left
  rw [div_eq_one_iff_eq h_sin]

theorem algebra_155709_1 {A B C : ℝ} {n : ℤ} (h : A + B + C = π)
  (hnz : 1 - tan (n * A) * tan (n * B) ≠ 0)
  (hadd : ((∀ (k : ℤ), n * A ≠ (2 * k + 1) * π/2) ∧ ∀ (l : ℤ), n * B ≠ (2 * l + 1) * π/2) ∨
  (∃ (k : ℤ), n * A = (2 * k + 1) * π/2) ∧ ∃ (l : ℤ), n * B = (2 * l + 1) * π/2) :
  tan (n * A) + tan (n * B) + tan (n * C) = tan (n * A) * tan (n * B) * tan (n * C) := by
  -- Conclude using A + B + C = π and tan identities
  rw [show C = π - A - B by linarith, show n * (π - A - B) = n * π - (n * A + n * B) by ring,
      Real.tan_int_mul_pi_sub, tan_add hadd]
  field_simp
  ring

lemma lemma_2 {x y : ℝ} (hx_sin : sin x ≠ 0) (hy : sin y ≠ 0) (hxy : cos (x + y) ≠ 0)
  : tan (x + y) = (cot x + cot y) / (cot x * cot y - 1) := by
  have hxy' : cos x * cos y - sin x * sin y ≠ 0
  · rw [←cos_add]; exact hxy
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, tan_eq_sin_div_cos, sin_add, cos_add]
  field_simp
  ring

theorem algebra_155709_2 {A B C : ℝ} {n : ℤ} (h : A + B + C = π) (h_odd : Odd n)
  (hA : sin (n * A / 2) ≠ 0) (hB : sin (n * B / 2) ≠ 0) (hAB : cos (n * A / 2 + n * B / 2) ≠ 0)
  : cot (n * A / 2) + cot (n * B / 2) + cot (n * C / 2) =
  cot (n * A / 2) * cot (n * B / 2) * cot (n * C / 2) := by
  -- Conclude using cot identities
  obtain ⟨k, hk⟩ := h_odd
  have h1 : n * C / 2 = (2 * k + 1) * π / 2 - (n * A / 2 + n * B / 2)
  · trans (2 * k + 1) * (π - A - B) / 2
    · field_simp [hk]; left; linarith
    · field_simp [hk]; ring
  rw [h1, lemma_1, lemma_2 hA hB hAB]
  have : cot (n * A / 2) * cot (n * B / 2) - 1 ≠ 0
  · rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin]
    field_simp
    rw [←cos_add]
    exact hAB
  field_simp
  ring