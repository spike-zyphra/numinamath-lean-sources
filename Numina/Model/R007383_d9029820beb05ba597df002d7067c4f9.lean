import Mathlib

open Real Set

theorem inequalities_9164 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    (a ^ 4 / (b ^ 2 + c) + b ^ 4 / (c ^ 2 + a) + c ^ 4 / (a ^ 2 + b) ≥ 3 / 2)
    ∧ ((a = 1 ∧ b = 1) →  (a ^ 4 / (b ^ 2 + c) + b ^ 4 / (c ^ 2 + a) + c ^ 4 / (a ^ 2 + b) = 3 / 2)) := by
  constructor
  -- Prove the inequality part
  ·
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 4 / (y ^ 2 + z) + (y ^ 2 + z) / 4 ≥ x ^ 2 := by
        intros x y z hx hy hz
        have h2 : y ^ 2 + z > 0 := by nlinarith [sq_nonneg y, hz]
        have h3 : x ^ 4 / (y ^ 2 + z) + (y ^ 2 + z) / 4 - x ^ 2 ≥ 0 := by
          have h4 : (x ^ 2 - (y ^ 2 + z) / 2) ^ 2 ≥ 0 := sq_nonneg _
          have h5 : x ^ 4 / (y ^ 2 + z) + (y ^ 2 + z) / 4 - x ^ 2 = (x ^ 2 - (y ^ 2 + z) / 2) ^ 2 / (y ^ 2 + z) := by
            field_simp
            ring
          rw [h5]
          have h6 : (y ^ 2 + z) > 0 := by nlinarith [sq_nonneg y, hz]
          exact div_nonneg h4 (by linarith [sq_nonneg y, hz])
        nlinarith [h3]
    have h2 := h1 a b c ha hb hc
    have h3 := h1 b c a hb hc ha
    have h4 := h1 c a b hc ha hb
    have h5 : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h6 : a + b + c = 3 := h
    have h7 : a ^ 2 + b ^ 2 + c ^ 2 ≥ (3 : ℝ)/ 2 := by nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), h6]
    have h10 : a ^ 4 / (b ^ 2 + c) + (b ^ 2 + c) / 4 ≥ a ^ 2 := by
      have h11 : a ^ 4 / (b ^ 2 + c) + (b ^ 2 + c) / 4 ≥ a ^ 2 := by nlinarith [h2, h6]
      linarith
    have h10b : b ^ 4 / (c ^ 2 + a) + (c ^ 2 + a) / 4 ≥ b ^ 2 := by
      have h11 : b ^ 4 / (c ^ 2 + a) + (c ^ 2 + a) / 4 ≥ b ^ 2 := by nlinarith [h3, h6]
      linarith
    have h10c : c ^ 4 / (a ^ 2 + b) + (a ^ 2 + b) / 4 ≥ c ^ 2 := by
      have h11 : c ^ 4 / (a ^ 2 + b) + (a ^ 2 + b) / 4 ≥ c ^ 2 := by nlinarith [h4, h6]
      linarith
    have h11 : a ^ 4 / (b ^ 2 + c) + b ^ 4 / (c ^ 2 + a) + c ^ 4 / (a ^ 2 + b) ≥ a ^ 2 + b ^ 2 + c ^ 2 - ( (b ^ 2 + c) + (c ^ 2 + a) + (a ^ 2 + b) ) / 4 := by
      linarith [h10, h10b, h10c]
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        h6, h5, h7, h11]
  · -- Prove the equality part when a = 1 and b = 1
    intro h
    rcases h with ⟨ha1, hb1⟩
    have hc1 : c = 1 := by
      nlinarith
    rw [ha1, hb1, hc1]
    norm_num