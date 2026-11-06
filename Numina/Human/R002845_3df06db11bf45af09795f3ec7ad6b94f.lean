import Mathlib

/- In the Cartesian coordinate system, the graph of the function $y=\frac{x+1}{|x|+1}$
has three different points on the line $l$, and the sum of the x-coordinates of these three points is 0.
Find the range of the slope of $l$.-/

theorem algebra_121163 (k b : ℝ) (hk: k ≠ 0) (h : ∃ x1 x2 x3 : ℝ, x1 < x2 ∧ x2 < x3 ∧
    x1 + x2 + x3 = 0 ∧ k * x1 + b = (x1 + 1) / (|x1| + 1) ∧
    k * x2 + b = (x2 + 1) / (|x2| + 1) ∧ k * x3 + b = (x3 + 1) / (|x3| + 1)) :
    0 < k ∧ k < 2 / 9 := by

    obtain ⟨x1, x2, x3, r1, r2, s, h1, h2, h3⟩ := h

    -- we first show that 0 ≤ x3
    have l3: 0 ≤ x3 := by
        linarith
    rw [show |x3| = x3 by apply abs_of_nonneg; linarith] at h3
    have o3: x3 + 1 ≠ 0 := by
        linarith
    field_simp at h3
    clear o3


    -- then we show that x2 ≤ 0
    have l2: x2 ≤ 0 := by
        by_contra! o
        rw [show |x2| = x2 by apply abs_of_nonneg; linarith] at h2
        have o2: x2 + 1 ≠ 0 := by
            linarith
        field_simp at h2
        have v: k * (x2 - x3) = 0 := by linarith
        simp at v
        simp [hk] at v
        linarith

    -- then we can take out the abs sign
    rw [show |x2| = -x2 by apply abs_of_nonpos; linarith] at h2
    rw [show |x1| = -x1 by apply abs_of_nonpos; linarith] at h1
    have o2: -x2 + 1 ≠ 0 := by
        linarith
    have o1: -x1 + 1 ≠ 0 := by
        linarith
    field_simp at h1 h2
    clear o1 o2

    -- use vieta's lemma to derive x1 + x2
    have u: (x1 - x2) * (-k * (x1 + x2) + k - b - 1) = 0 := by
        clear *- h1 h2
        nlinarith
    have v: x1 - x2 ≠ 0 := by linarith
    simp [v] at u
    clear v

    -- then we show that k = 2b
    have f: k = 2 * b := by
        replace u: k * (x1 + x2) = (k - b - 1) := by
            linarith
        have q: k * (x1 + x2 + x3) = k - 2 * b := by
            clear *- h3 u
            nlinarith
        simp [s] at q
        linarith

    simp [f] at *
    have i: 0 < b := by
        nlinarith
    refine ⟨i, ?_⟩
    have s: b < 1 := by
        nlinarith

    -- finally, we show b < 1 / 9 by 0 < Δ
    clear *- r1 h1 h2 i s
    have g1:= h1
    replace h1: (1 - b) * (1 - 9 * b) = (4 * b * x1 + 1 - b) ^ 2 := by
        clear *- h1
        suffices (4 * b * x1 + 1 - b) ^ 2 - (1 - b) * (1 - 9 * b) = 0 by linarith
        ring_nf
        replace h1: (2 * b * x1 + b) * (-x1 + 1) - x1 - 1 = 0 := by linarith
        ring_nf at h1
        rw [show b * 8 + b * x1 * 8 + (-(b ^ 2 * 8) - b ^ 2 * x1 * 8) + b ^ 2 * x1 ^ 2 * 16 =
        b * (8 + x1 * 8 + (-(b * 8) - b * x1 * 8) + b * x1 ^ 2 * 16) by ring]
        suffices 8 + x1 * 8 + (-(b * 8) - b * x1 * 8) + b * x1 ^ 2 * 16 = 0 by simp [this]
        nlinarith
    replace h1: 0 ≤ (1 - b) * (1 - 9 * b) := by rw [h1]; nlinarith
    have f:= nonneg_of_mul_nonneg_right h1 (by linarith)
    suffices b ≠ 1 / 9 by
        by_contra! o
        replace o: b = 1 / 9 := by linarith
        tauto
    by_contra! o
    simp [o] at g1 h2
    replace g1: (x1 + 2) ^ 2 = 0 := by
        nlinarith
    simp at g1
    replace h2: (x2 + 2) ^ 2 = 0 := by
        nlinarith
    simp at h2
    linarith