import Mathlib

open Real Set
open scoped BigOperators

/- Non-empty set $A=\left{ x|-2\leqslant x\leqslant a \right}$, $B=\left{ y|y=2x+3,x\in A \right}$, $C=\left{ z|z={{x}^{2}},x\in A \right}$, if $C\subseteq B$, then the range of values for $a$ is ___          ___. -/
theorem algebra_12619 {a : ℝ} (ha : -2 ≤ a) (B C : Set ℝ)
  (hB : B = {y | ∃ x, y = 2 * x + 3 ∧ -2 ≤ x ∧ x ≤ a})
  (hC : C = {z | ∃ x, z = x ^ 2 ∧ -2 ≤ x ∧ x ≤ a}) :
  C ⊆ B ↔ 1 / 2 ≤ a ∧ a ≤ 3 := by
  constructor
  · -- Assume C ⊆ B
    intro h
    have h1 : 1 / 2 ≤ a := by
      have h4_in_C : (4 : ℝ) ∈ C := by
        rw [hC]
        use -2
        norm_num
        all_goals nlinarith
      have h4_in_B : (4 : ℝ) ∈ B := h h4_in_C
      rw [hB] at h4_in_B
      rcases h4_in_B with ⟨x, hx_eq, hx1, hx2⟩
      nlinarith
    have h2 : a ≤ 3 := by
      have ha2_in_C : a ^ 2 ∈ C := by
        rw [hC]
        use a
        all_goals nlinarith
      have ha2_in_B : a ^ 2 ∈ B := h ha2_in_C
      rw [hB] at ha2_in_B
      rcases ha2_in_B with ⟨x, hx_eq, hx1, hx2⟩
      nlinarith [sq_nonneg (x - a), sq_nonneg (a - 3), sq_nonneg (a), sq_nonneg (x + 1)]
    constructor <;> linarith
  · -- Assume 1/2 ≤ a ∧ a ≤ 3
    rintro ⟨ha1, ha2⟩
    intro z hz
    rw [hC] at hz
    rcases hz with ⟨x, hxz, hx1, hx2⟩
    have hw : ∃ w, z = 2 * w + 3 ∧ -2 ≤ w ∧ w ≤ a := by
      use (x ^ 2 - 3) / 2
      constructor
      · -- Show z = 2 * w + 3
        nlinarith
      constructor
      · -- Show -2 ≤ w
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 3), sq_nonneg (x - a), sq_nonneg (a - 3)]
      · -- Show w ≤ a
        nlinarith [sq_nonneg (x - a), sq_nonneg (x - 3), sq_nonneg (a - 3), sq_nonneg (x - a), sq_nonneg (x), sq_nonneg (a), mul_nonneg (show 0 ≤ a + 2 by linarith) (show 0 ≤ a - (-2) by linarith)]
    rcases hw with ⟨w, hwz, hw1, hw2⟩
    rw [hB]
    refine ⟨w, by linarith, hw1, hw2⟩