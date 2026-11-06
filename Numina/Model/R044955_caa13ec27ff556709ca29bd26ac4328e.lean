import Mathlib

open Set

theorem algebra_128626 {a : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = a * x ^ 2 + x) :
    (a < 0 → ∀ x1 x2, f ((x1 + x2) / 2) ≥ (f x1 + f x2) / 2) ∧
    ((∀ x ∈ Icc 0 1, |f x| ≤ 1) ↔ a ∈ Ico (-2) 0) := by
  constructor
  · -- Proof that when a < 0, f is convex.
    intro ha x1 x2
    have h1 : f ((x1 + x2) / 2) = a * ((x1 + x2) / 2) ^ 2 + (x1 + x2) / 2 := by
      rw [hf]
    have h2 : f x1 = a * x1 ^ 2 + x1 := by
      rw [hf]
    have h3 : f x2 = a * x2 ^ 2 + x2 := by
      rw [hf]
    rw [h1, h2, h3]
    have h4 : a < 0 := ha
    suffices - a / 4 * (x1 - x2) ^ 2 ≥ 0 by
      linarith
    have h5 : - a / 4 ≥ 0 := by nlinarith [sq_nonneg (x1 - x2)]
    have h6 : (x1 - x2) ^ 2 ≥ 0 := sq_nonneg (x1 - x2)
    nlinarith
  · -- Proof for the range of a.
    constructor
    · -- Assume that for all x in [0,1], |f x| ≤ 1, prove that a ∈ Ico (-2) 0
      intro h
      have h1 : a ≤ 0 := by
        have h2 := h 1 (by norm_num)
        have h3 : -1 ≤ f 1 ∧ f 1 ≤ 1 := by
          constructor
          · linarith [abs_le.mp h2]
          · linarith [abs_le.mp h2]
        have h4 : f 1 = a * (1:ℝ)^2 + 1 := by
          rw [hf]
        rw [h4] at h3
        nlinarith
      have ha1 : a ≥ -2 := by
        have h2 := h 0 (by norm_num)
        have h3 := h 1 (by norm_num)
        have h4 : f 0 = 0 := by
          rw [hf]
          norm_num
        have h5 : f 1 = a + 1 := by
          rw [hf]
          ring
        have h6 : f 0 ≥ -1 := by
          have h7 : |f 0| ≤ 1 := by simpa using h2
          linarith [abs_le.mp h7]
        have h7 : f 1 ≤ 1 := by
          have h8 : |f 1| ≤ 1 := by simpa using h3
          linarith [abs_le.mp h8]
        have h8 : f 1 ≥ -1 := by
          have h9 : |f 1| ≤ 1 := by simpa using h3
          linarith [abs_le.mp h9]
        nlinarith
      have h9 : a < 0 := by
        by_contra h10
        push_neg at h10
        have h10 : a = 0 := by 
          linarith
        have h11 : a = 0 := h10
        tauto
      constructor
      · linarith
      · linarith
    · -- Assume a ∈ Ico (-2) 0, prove that ∀ x ∈ [0,1], |f x| ≤ 1
      rintro ⟨ha1, ha2⟩
      intro x hx
      have h1 : 0 ≤ x := by
        have hx1 : x ∈ Icc (0 : ℝ) 1 := hx
        simp at hx1 ⊢
        linarith
      have h2 : x ≤ 1 := by
        have hx1 : x ∈ Icc (0 : ℝ) 1 := hx
        simp at hx1 ⊢
        linarith
      have h3 : f x = a * x^2 + x := by
        rw [hf]
      have h4 : -1 ≤ a * x ^ 2 + x ∧ a * x ^ 2 + x ≤ 1 := by
        constructor
        · -- Show that a * x^2 + x ≥ -1
          nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 0), sq_nonneg (a), sq_nonneg (x - 1 / 2), sq_nonneg (a * (x ^ 2 - 1 / 2)), sq_nonneg (a + 2), mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ x by linarith)]
        · -- Show that a * x^2 + x ≤ 1
          nlinarith [sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (a), sq_nonneg (x - 1 / 2), sq_nonneg (a + 2), sq_nonneg (x^2 - 1 / 2), mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ x by linarith)]
      have h5 : -1 ≤ a * x ^ 2 + x ∧ a * x ^ 2 + x ≤ 1 := h4
      have h6 : -1 ≤ f x ∧ f x ≤ 1 := by
        rw [h3] at *
        exact h4
      apply abs_le.mpr
      constructor <;> linarith [h6.1, h6.2]