import Mathlib

theorem algebra_1109 (k : ℝ) (hk : 0 < k ∧ k < 1) (y : ℝ → ℝ)
    (hy : ∀ x, y x = (k - 1 / k) * x + 1 / k) :
    IsGreatest (Set.image y (Set.Icc 1 2)) k := by
  constructor
  · -- Show k is attainable, i.e., there exists x in [1, 2] such that y x = k
    use 1
    constructor
    · -- Show 1 ∈ [1, 2]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show y 1 = k
      have h1 : y 1 = (k - 1 / k) * (1 : ℝ) + 1 / k := by
        specialize hy 1
        simpa using hy
      rw [h1]
      ring
  · -- Show k is the greatest element in the image
    intro y_val
    rintro ⟨x, hx, hfx⟩
    have hx1 : 1 ≤ x := by
      linarith [hx.1]
    have hx2 : x ≤ 2 := by
      linarith [hx.2]
    have hy_x : y x = (k - 1 / k) * x + 1 / k := by
      apply hy
    rw [hy_x] at hfx
    have h_neg : k - 1 / k < 0 := by
      have hk1 : 0 < k := hk.1
      have hk2 : k < 1 := hk.2
      have h1 : 1 / k > 0 := by positivity
      have h2 : 1 / k > 1 := by
        have hk3 : k > 0 := hk1
        have hk4 : k < 1 := hk2
        have : 1 / k - 1 > 0 := by
          have hk5 : 1 - k > 0 := by linarith
          have hk6 : 0 < k := hk1
          have hk7 : (1 - k) / k > 0 := by
            apply div_pos (by linarith) (by linarith)
          have hk8 : (1 / k) - 1 = (1 - k) / k := by
            field_simp
            <;> linarith
          rw [hk8] at *
          linarith
        linarith
      linarith
    nlinarith [h_neg, hx1, hx2, mul_self_nonneg (k - 1), mul_self_nonneg (k - 1 / k)]