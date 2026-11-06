import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_294821 (f : ℝ → ℝ) (hf : f = λ x => sin x / (2 - cos x)) :
    IsGreatest (range f) (sqrt 3 / 3) := by
  constructor
  · -- Show that sqrt 3 / 3 is in the range of f
    use Real.pi / 3
    rw [hf]
    have h1 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
      rw [sin_pi_div_three]
    have h2 : cos (Real.pi / 3) = 1 / 2 := by
      rw [cos_pi_div_three]
    simp [h1, h2]
    field_simp
    <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr]
  · -- Show that sqrt 3 / 3 is the greatest value in the range
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h3 : 2 - cos x > 0 := by
      nlinarith [cos_le_one x, neg_one_le_cos x]
    have h4 : 3 * sin x ≤ Real.sqrt 3 * (2 - cos x) := by
      nlinarith [sq_nonneg (sin x - Real.sqrt 3 / 2), sq_nonneg (cos x - 1 / 2),
        Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        sq_nonneg (Real.sqrt 3 * cos x - sin x),
        sq_nonneg (sin x * 2 - Real.sqrt 3 * (2 - cos x)),
        sq_nonneg (sin x), sq_nonneg (cos x - 1 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num),
        sq_nonneg (sqrt 3 * sin x - cos x * 1),
        Real.sqrt_nonneg 3,
        sin_sq_add_cos_sq x
      ]
    have h5 : sin x / (2 - cos x) ≤ Real.sqrt 3 / 3 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h4]
    linarith [hx, h5]