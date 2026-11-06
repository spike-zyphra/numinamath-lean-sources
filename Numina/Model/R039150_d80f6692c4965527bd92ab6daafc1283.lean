import Mathlib

theorem inequalities_27521 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hsum : a + b + c + d = 1) :
    1 / 2 ≤ a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + d) + d ^ 2 / (d + a) ∧
    (1 / 2 = a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + d) + d ^ 2 / (d + a) ↔
      (a = b ∧ b = c ∧ c = d)) := by
  have h1 : a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + d) + d ^ 2 / (d + a) ≥ 1 / 2 := by
    have h1 : a ^ 2 / (a + b) ≥ (3 * a - b) / 4 := by
      have hpos : 0 < a + b := by nlinarith
      apply (le_div_iff₀ hpos).mpr
      nlinarith [sq_nonneg (a - b)]
    have h2 : b ^ 2 / (b + c) ≥ (3 * b - c) / 4 := by
      have hpos : 0 < b + c := by nlinarith
      apply (le_div_iff₀ hpos).mpr
      nlinarith [sq_nonneg (b - c)]
    have h3 : c ^ 2 / (c + d) ≥ (3 * c - d) / 4 := by
      have hpos : 0 < c + d := by nlinarith
      apply (le_div_iff₀ hpos).mpr
      nlinarith [sq_nonneg (c - d)]
    have h4 : d ^ 2 / (d + a) ≥ (3 * d - a) / 4 := by
      have hpos : 0 < d + a := by nlinarith
      apply (le_div_iff₀ hpos).mpr
      nlinarith [sq_nonneg (d - a)]
    linarith [h1, h2, h3, h4, hsum]
  have h2 : 1 / 2 = a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + d) + d ^ 2 / (d + a) ↔ (a = b ∧ b = c ∧ c = d) := by
    constructor
    · -- Assume equality holds, so $\frac{a^2}{a+b} + \frac{b^2}{b+c} + \frac{c^2}{c+d} + \frac{d^2}{d+a} = \frac{1}{2}$, show $a = b = c = d$
      intro heq
      have h1 : a + b + c + d = 1 := hsum
      have h5 : a ^ 2 / (a + b) ≥ (3 * a - b) / 4 := by
        have hpos : 0 < a + b := by nlinarith
        apply (le_div_iff₀ hpos).mpr
        nlinarith [sq_nonneg (a - b)]
      have h6 : b ^ 2 / (b + c) ≥ (3 * b - c) / 4 := by
        have hpos : 0 < b + c := by nlinarith
        apply (le_div_iff₀ hpos).mpr
        nlinarith [sq_nonneg (b - c)]
      have h7 : c ^ 2 / (c + d) ≥ (3 * c - d) / 4 := by
        have hpos : 0 < c + d := by nlinarith
        apply (le_div_iff₀ hpos).mpr
        nlinarith [sq_nonneg (c - d)]
      have h8 : d ^ 2 / (d + a) ≥ (3 * d - a) / 4 := by
        have hpos : 0 < d + a := by nlinarith
        apply (le_div_iff₀ hpos).mpr
        nlinarith [sq_nonneg (d - a)]
      have h9 : a ^ 2 / (a + b) = (3 * a - b) / 4 := by linarith [h5, heq, h1]
      have hab : a = b := by
        have hpos : 0 < a + b := by nlinarith
        field_simp at h9
        nlinarith [sq_nonneg (a - b)]
      have h10 : b ^ 2 / (b + c) = (3 * b - c) / 4 := by linarith [h6, heq, h1]
      have hbc : b = c := by
        have hpos : 0 < b + c := by nlinarith
        field_simp at h10
        nlinarith [sq_nonneg (b - c)]
      have h11 : c ^ 2 / (c + d) = (3 * c - d) / 4 := by linarith [h7, heq, h1]
      have hcd : c = d := by
        have hpos : 0 < c + d := by nlinarith
        field_simp at h11
        nlinarith [sq_nonneg (c - d)]
      have h12 : d ^ 2 / (d + a) = (3 * d - a) / 4 := by linarith [h8, heq, h1]
      have hda : d = a := by
        have hpos : 0 < d + a := by nlinarith
        field_simp at h12
        nlinarith [sq_nonneg (d - a)]
      exact ⟨hab, hbc, hcd⟩
    · -- Assume $a = b = c = d$, show $\frac{a^2}{a+b} + \frac{b^2}{b+c} + \frac{c^2}{c+d} + \frac{d^2}{d+a} = \frac{1}{2}$
      rintro ⟨rfl, rfl, rfl⟩
      have h1 : 4 * a = 1 := by
        nlinarith
      have ha : a = 1 / 4 := by
        linarith
      rw [ha]
      norm_num
  constructor
  · linarith [h1]
  · exact h2