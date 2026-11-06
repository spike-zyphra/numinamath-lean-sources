import Mathlib

open BigOperators Real Set

lemma lemma_1 (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    sqrt (A ^ 2 + B ^ 2) / (A + 2 * B) ≥ sqrt 5 / 5 := by
  have h1 : 0 < A + 2 * B := by
    linarith
  have h6 : sqrt (A ^ 2 + B ^ 2) / (A + 2 * B) ≥ sqrt 5 / 5 := by
    have h11 : 0 < A + 2 * B := by linarith
    have h12 : 0 < (A + 2 * B : ℝ) := by linarith
    have h9 : 0 < (5 : ℝ) := by norm_num
    have h14 : (2 * A - B) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h15 : 5 * (A ^ 2 + B ^ 2) ≥ (A + 2 * B) ^ 2 := by
      nlinarith [sq_nonneg (2 * A - B)]
    have h16 : (sqrt (A ^ 2 + B ^ 2) : ℝ) * 5 ≥ (sqrt 5 * (A + 2 * B)) := by
      have h17 : ((sqrt (A ^ 2 + B ^ 2) : ℝ) * 5) ^ 2 ≥ (sqrt 5 * (A + 2 * B)) ^ 2 := by
        have h18 : ((sqrt (A ^ 2 + B ^ 2) : ℝ) * 5) ^ 2 = 25 * (A ^ 2 + B ^ 2) := by
          calc
            ((sqrt (A ^ 2 + B ^ 2) : ℝ) * 5) ^ 2 = (sqrt (A ^ 2 + B ^ 2)) ^ 2 * 25 := by ring_nf
            _ = (A ^ 2 + B ^ 2) * 25 := by
              rw [Real.sq_sqrt]
              positivity
            _ = 25 * (A ^ 2 + B ^ 2) := by ring
        have h19 : (sqrt 5 * (A + 2 * B)) ^ 2 = 5 * (A + 2 * B) ^ 2 := by
          calc
            (sqrt 5 * (A + 2 * B)) ^ 2 = (sqrt 5 : ℝ) ^ 2 * (A + 2 * B) ^ 2 := by ring_nf
            _ = (5 : ℝ) * (A + 2 * B) ^ 2 := by
              rw [Real.sq_sqrt]
              all_goals norm_num
            _ = 5 * (A + 2 * B) ^ 2 := by ring
        have h20 : 25 * (A ^ 2 + B ^ 2) ≥ 5 * (A + 2 * B) ^ 2 := by
          nlinarith [h15]
        nlinarith [h18, h19, h20]
      have h22 : 0 ≤ (sqrt 5 * (A + 2 * B) : ℝ) := by
        positivity
      have h21 : 0 ≤ ((sqrt (A ^ 2 + B ^ 2) : ℝ) * 5) := by
        positivity
      nlinarith [Real.sqrt_nonneg (A ^ 2 + B ^ 2), Real.sqrt_nonneg (5 : ℝ), h17]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg (A ^ 2 + B ^ 2), Real.sqrt_nonneg (5 : ℝ), h16]
  linarith [h6]


theorem inequalities_299717 :
  IsLeast {f | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ f = (sqrt (x^2 + y^2) + sqrt (y^2 + 4 * z^2) + sqrt (z^2 + 16 * x^2)) / (9 * x + 3 * y + 5 * z)} (sqrt 5 / 5) := by
  constructor
  · -- Show sqrt 5 / 5 ∈ {f | ...}
    use 1, 2, 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    have h1 : sqrt (1 ^ 2 + (2 : ℝ) ^ 2) = Real.sqrt 5 := by
      ring_nf
    have h2 : sqrt ((2 : ℝ) ^ 2 + 4 * (2 : ℝ) ^ 2) = Real.sqrt 20 := by
      ring_nf
    have h3 : sqrt ((2 : ℝ) ^ 2 + 16 * (1 : ℝ) ^ 2) = Real.sqrt 20 := by
      ring_nf
    rw [h1, h2, h3]
    have h4 : Real.sqrt 20 = 2 * Real.sqrt 5 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h4]
    field_simp
    ring_nf
  · -- Show sqrt 5 / 5 is the least element in the set
    intro f hf
    rcases hf with ⟨x, y, z, hx, hy, hz, hf⟩
    have h10 : sqrt (x ^ 2 + y ^ 2) ≥ Real.sqrt 5 / 5 * (x + 2 * y) := by
      have h11 : sqrt (x ^ 2 + y ^ 2) / (x + 2 * y) ≥ Real.sqrt 5 / 5 := by
        have h12 : x + 2 * y > 0 := by
          nlinarith [hx, hy]
        apply lemma_1 x y hx hy
      have h14 : x + 2 * y > 0 := by
        nlinarith [hx, hy]
      have h15 : sqrt (x ^ 2 + y ^ 2) ≥ Real.sqrt 5 / 5 * (x + 2 * y) := by
        have h16 : sqrt (x ^ 2 + y ^ 2) / (x + 2 * y) ≥ Real.sqrt 5 / 5 := h11
        apply (le_div_iff₀ (by linarith)).mp at h16
        linarith
      linarith
    have h11 : sqrt (y ^ 2 + 4 * z ^ 2) ≥ Real.sqrt 5 / 5 * (y + 4 * z) := by
      have h22 : sqrt (y ^ 2 + 4 * z ^ 2) / (y + 4 * z) ≥ Real.sqrt 5 / 5 := by
        have h23 : y + 4 * z > 0 := by
          nlinarith [hy, hz]
        have hA1 : sqrt (y ^ 2 + 4 * z ^ 2) / (y + 4 * z) ≥ Real.sqrt 5 / 5 := by
          have hA11 : sqrt ((y) ^ 2 + (2 * z) ^ 2) / (y + 2 * (2 * z)) ≥ Real.sqrt 5 / 5 := by
            apply lemma_1 y (2 * z) (by positivity) (by positivity)
          have hA22 : sqrt (y ^ 2 + 4 * z ^ 2) / (y + 4 * z) = sqrt ((y) ^ 2 + (2 * z) ^ 2) / (y + 2 * (2 * z)) := by
            ring_nf
          rw [hA22]
          all_goals linarith [hA11]
        linarith
      have h24 : y + 4 * z > 0 := by
        nlinarith [hy, hz]
      have h25 : sqrt (y ^ 2 + 4 * z ^ 2) ≥ Real.sqrt 5 / 5 * (y + 4 * z) := by
        have h26 : sqrt (y ^ 2 + 4 * z ^ 2) / (y + 4 * z) ≥ Real.sqrt 5 / 5 := h22
        apply (le_div_iff₀ (by linarith)).mp at h26
        linarith
      linarith
    have h24 : sqrt (z ^ 2 + 16 * x ^ 2) ≥ Real.sqrt 5 / 5 * (z + 8 * x) := by
      have h222 : sqrt (z ^ 2 + 16 * x ^ 2) / (z + 8 * x) ≥ Real.sqrt 5 / 5 := by
        have h233 : z + 8 * x > 0 := by
          nlinarith [hz, hx]
        have hA1 : sqrt (z ^ 2 + 16 * x ^ 2) / (z + 8 * x) ≥ Real.sqrt 5 / 5 := by
          have hA11 : sqrt ((z) ^ 2 + (4 * x) ^ 2) / (z + 2 * (4 * x)) ≥ Real.sqrt 5 / 5 := by
            apply lemma_1 z (4 * x) (by positivity) (by positivity)
          have hA22 : sqrt (z ^ 2 + 16 * x ^ 2) / (z + 8 * x) = sqrt ((z) ^ 2 + (4 * x) ^ 2) / (z + 2 * (4 * x)) := by
            ring_nf
          rw [hA22]
          all_goals linarith [hA11]
        linarith
      have h244 : z + 8 * x > 0 := by
        nlinarith [hz, hx]
      have h255 : sqrt (z ^ 2 + 16 * x ^ 2) ≥ Real.sqrt 5 / 5 * (z + 8 * x) := by
        have h266 : sqrt (z ^ 2 + 16 * x ^ 2) / (z + 8 * x) ≥ Real.sqrt 5 / 5 := h222
        apply (le_div_iff₀ (by linarith)).mp at h266
        linarith
      linarith
    have h33 : sqrt (x ^ 2 + y ^ 2) + sqrt (y ^ 2 + 4 * z ^ 2) + sqrt (z ^ 2 + 16 * x ^ 2) ≥ Real.sqrt 5 / 5 * (9 * x + 3 * y + 5 * z) := by
      nlinarith [h10, h11, h24]
    have h44 : 9 * x + 3 * y + 5 * z > 0 := by
      positivity
    have h55 : (sqrt (x^2 + y^2) + sqrt (y^2 + 4 * z^2) + sqrt (z^2 + 16 * x^2)) / (9 * x + 3 * y + 5 * z) ≥ Real.sqrt 5 / 5 := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith [h33]
    linarith [hf, h55]