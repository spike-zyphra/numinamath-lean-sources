import Mathlib
/- An infinite geometric series has common ratio $-1/5$ and sum $16.$  What is the first term of the series? -/
theorem algebra_14164 {a : ℝ} (h : a ≠ 0) (r : ℚ) (h₀ : r = -1 / 5) (h₁ : ∑' n : ℕ, a * r ^ n = 16) :
    a = 96 / 5 := by
  -- the "geom_series_eq_inverse" is a theorem from new mathlib library. Maybe it can be found in Mathlib.Analysis.SpecificLimits.Normed. Here we write a more convenient form.
  have geom_series_eq_inverse'(x : ℝ)(h : ‖x‖ < 1):
    ∑' i, x ^ i = Ring.inverse (1 - x) := by
    change (Units.oneSub x h) ⁻¹ = Ring.inverse (1 - x)
    rw [← Ring.inverse_unit]
    rfl
  -- recall that when |x|<1, 1+x+x^2+...=1/(1-x). therefore a+ar+ar^2+... = a/(1-r), when |r| < 1
  have geo_sum: ∑' n:ℕ, a*r^n = a/(1-r) := by
    have h0: |(1/5:ℝ)| = 1/5 := by
      have: 0 < (1/5:ℝ) := by norm_num
      apply abs_of_pos this
    have h1: ∑' n:ℕ, a*r^n = a * (∑' n:ℕ, (r^n:ℝ)) := by
      have ht1: |(r:ℝ)| < 1 := by
        rw [h₀]; simp; norm_num; rw [h0]; norm_num
      have ht2 := summable_geometric_of_abs_lt_one ht1
      apply Summable.tsum_mul_left a ht2
    have h2: ∑' n:ℕ, (r^n:ℝ) = 1/(1-r) := by
      have ht1: ‖r‖ < 1 := by
        have ht1: ‖r‖ = |(r:ℝ)| := rfl
        rw [ht1, h₀]; norm_num
        rw [h0]; norm_num
      rw [geom_series_eq_inverse' (r:ℝ) ht1]
      simp
    rw [h1, h2]; ring
  -- substitute geometric series sum equation and r=-1/5 into h₁
  rw [geo_sum, h₀] at h₁
  -- then we can solve a=96/5
  have: (96:ℝ) = 16*6 := by norm_num
  rw [this, ← h₁]; ring