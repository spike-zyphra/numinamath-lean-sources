import Mathlib

theorem algebra_315649 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hroots : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0) :
    max (max a b) c ≥ (4 / 9) * (a + b + c) ∧
    min (min a b) c ≤ (1 / 4) * (a + b + c) := by
  rcases hroots with ⟨x, hx⟩
  have h1 : b ^ 2 - 4 * a * c ≥ 0 := by
    nlinarith [sq_nonneg (2 * a * x + b), sq_nonneg (x * a + b / 2), sq_nonneg (x + b / (2 * a)), sq_nonneg (x * (2 * a) + b), sq_nonneg ((2 * a * x + b)), sq_nonneg ((x * (2 * a) + b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  constructor
  · -- Prove max (max a b) c ≥ (4 / 9) * (a + b + c)
    by_contra h
    push_neg at h
    have h2 : max (max a b) c < (4 / 9) * (a + b + c) := h
    have h3 : a < (4 / 9) * (a + b + c) := by
      have h4 : a ≤ max (max a b) c := by
        simp [max_le_iff]
      nlinarith [h4, h2]
    have h4 : b < (4 / 9) * (a + b + c) := by
      have h5 : b ≤ max (max a b) c := by
        simp [max_le_iff]
      nlinarith [h5, h2]
    have h5 : c < (4 / 9) * (a + b + c) := by
      have h6 : c ≤ max (max a b) c := by
        simp [max_le_iff]
      nlinarith [h6, h2]
    nlinarith [sq_nonneg (a - b / 2), sq_nonneg (b - 2 * a), sq_nonneg (b - 2 * c), sq_nonneg (a - c), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1]
  · -- Prove min (min a b) c ≤ (1 / 4) * (a + b + c)
    by_contra h
    push_neg at h
    have h2 : min (min a b) c > (1 / 4) * (a + b + c) := h
    have h3 : a > (1 / 4) * (a + b + c) := by
      have h4 : a ≥ min (min a b) c := by
        simp [min_le_iff]
      nlinarith [h4, h2]
    have h4 : b > (1 / 4) * (a + b + c) := by
      have h5 : b ≥ min (min a b) c := by
        simp [min_le_iff]
      nlinarith [h5, h2]
    have h5 : c > (1 / 4) * (a + b + c) := by
      have h6 : c ≥ min (min a b) c := by
        simp [min_le_iff]
      nlinarith [h6, h2]
    nlinarith [sq_nonneg (a - b / 2), sq_nonneg (b - 2 * a), sq_nonneg (b - 2 * c), sq_nonneg (a - c), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1]