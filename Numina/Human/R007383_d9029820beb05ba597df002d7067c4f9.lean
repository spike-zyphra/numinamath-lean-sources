import Mathlib

open Real Set

theorem inequalities_9164 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    (a ^ 4 / (b ^ 2 + c) + b ^ 4 / (c ^ 2 + a) + c ^ 4 / (a ^ 2 + b) ≥ 3 / 2)
    ∧ ((a = 1 ∧ b = 1) →  (a ^ 4 / (b ^ 2 + c) + b ^ 4 / (c ^ 2 + a) + c ^ 4 / (a ^ 2 + b) = 3 / 2)) := by 
  constructor
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
  have h5 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 := by
    have h6 : (a + b + c) ^ 2 = 9 := by
      rw [h]
      norm_num
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  nlinarith [h2, h3, h4, h5, h]
  -- equality condition
  intro ⟨ha₁, hb₁⟩
  rw [ha₁, hb₁] at h
  have hc₁ : c = 1 := by
    calc 
      _ = (1 + 1 + c) - 1 - 1 := by ring
      _ = 1 := by rw [h]; ring
  rw [ha₁,hb₁, hc₁]
  norm_num