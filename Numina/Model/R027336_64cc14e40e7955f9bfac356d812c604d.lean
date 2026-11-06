import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_246643 {x : ℝ} (hx : x ∈ Ioo 0 π) (b : ℝ) (hb : b > 1)
  (a : ℝ) (ha : a = logb b (sin x)) :
  logb b (cos x) = (1 / 2) * logb b (1 - b ^ (2 * a)) := by 
  rcases hx with ⟨hx0, hxpi⟩
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h2 : cos x ^ 2 + sin x ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq x
  have h3 : b ^ a = sin x := by
    rw [ha] -- a = logb b (sin x)
    field_simp [hb.ne.symm]
    all_goals linarith
  have h4 : cos x ^ 2 = 1 - (b ^ a) ^ 2 := by
    have h5 : cos x ^ 2 = 1 - sin x ^ 2 := by
      linarith [h2]
    have h6 : sin x = b ^ a := by
      linarith
    rw [h6] at h5
    linarith
  have h7 : (cos x) ^ 2 = 1 - b ^ (2 * a) := by
    have h8 : b ^ (2 * a) = (b ^ a) ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h8]
    linarith [h4]
  have h9 : logb b ((cos x) ^ 2) = logb b (1 - b ^ (2 * a)) := by
    rw [h7]
  have h10 : logb b ((cos x) ^ 2) = 2 * logb b (cos x) := by
    simp [logb_pow]
  have h11 : logb b (cos x) = (1 / 2) * logb b (1 - b ^ (2 * a)) := by
    linarith [h9, h10]
  exact h11