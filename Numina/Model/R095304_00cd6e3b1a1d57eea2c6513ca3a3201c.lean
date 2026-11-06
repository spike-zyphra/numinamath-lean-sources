import Mathlib

theorem algebra_12308 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IsLeast {x | ∃ t ∈ Set.Ioo 0 1, x = a^2 / t + b^2 / (1 - t)} ((a + b)^2) := by
  constructor
  · -- Show that $(a + b)^2$ is in the set
    use a / (a + b)
    constructor
    · -- Show that $t \in (0, 1)$
      have ht1 : 0 < a / (a + b) := by
        apply div_pos
        all_goals linarith
      have ht2 : a / (a + b) < 1 := by
        have h1 : 0 < b := hb
        have h2 : a < a + b := by linarith
        have h3 : a / (a + b) < 1 := by
          have h4 : a < a + b := by linarith
          have h5 : 0 < a + b := by linarith
          apply (div_lt_one (by linarith)).mpr
          linarith
        linarith
      exact ⟨ht1, ht2⟩
    · -- Show that $\frac{a^2}{t} + \frac{b^2}{1 - t} = (a + b)^2$
      field_simp
      <;> ring_nf <;> field_simp
  · -- Show that $(a + b)^2$ is the least in the set
    intro x hx
    rcases hx with ⟨t, ⟨ht1, ht2⟩, h_eq⟩
    -- Let's use the Cauchy-Schwarz inequality
    -- (a^2 / t + b^2 / (1 - t)) ≥ (a + b)^2
    have h1 : 0 < t := ht1
    have h2 : t < 1 := ht2
    have h3 : 0 < 1 - t := by linarith
    have h4 : a^2 / t + b^2 / (1 - t) ≥ (a + b) ^ 2 := by
      have h5 : 0 < t * (1 - t) := by
        apply mul_pos
        · linarith
        · linarith
      have h6 : a^2 / t + b^2 / (1 - t) - (a + b) ^ 2 ≥ 0 := by
        have h7 : a^2 / t + b^2 / (1 - t) - (a + b) ^ 2 =
            (a^2 * (1 - t) + b^2 * t - (a + b) ^ 2 * t * (1 - t)) / (t * (1 - t)) := by
          field_simp
          <;> ring
        rw [h7]
        have h8 : a^2 * (1 - t) + b^2 * t - (a + b) ^ 2 * t * (1 - t) ≥ 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a * (1 - t) - b * t), sq_nonneg (a * t - b * (1 - t)), sq_nonneg (a - b * t / (1 - t)), sq_nonneg (b - a * (1 - t) / t), mul_pos ha hb, mul_pos ha (show 0 < 1 - t from by linarith), mul_pos hb (show 0 < t by linarith)
          ]
        apply div_nonneg
        · linarith
        · -- Show denominator is non-negative
          positivity
      linarith
    have h123 : a^2 / t + b^2 / (1 - t) = x := by linarith [h_eq]
    linarith [h4, h_eq]