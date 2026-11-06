import Mathlib

open Set Real

/- Given the sets $A=\left\{ x\left| {{x}^{2}}-3x+2\leqslant 0 \right. \right\}$, $B=\left\{ x\left| \frac{1}{x-3}<{}a \right. \right\}$. If $A\subseteq B$, then the range of the real number $a$ is ___          ___. -/
theorem inequalities_12365 (a : ℝ) (A B : Set ℝ)
    (hA : A = {x | x ^ 2 - 3 * x + 2 ≤ 0}) (hB : B = {x | 1 / (x - 3) < a}) :
    A ⊆ B ↔ a > -1 / 2 := by
  constructor
  · -- Assume A ⊆ B, we need to prove a > -1/2
    intro h
    have h1 : 1 ∈ A := by
      rw [hA]
      norm_num
    have h2 : 1 ∈ B := h h1
    rw [hB] at h2
    simp at h2
    norm_num at h2
    linarith
  · -- Assume a > -1/2, we need to prove A ⊆ B
    intro ha x hx
    rw [hA] at hx
    have h1 : x ^ 2 - 3 * x + 2 ≤ 0 := hx
    have h2 : 1 ≤ x := by nlinarith
    have h3 : x ≤ 2 := by nlinarith
    have h4 : x - 3 ≠ 0 := by
      linarith
    have h5 : 1 / (x - 3) < a := by
      have h6 : x - 3 < 0 := by linarith
      have h7 : x - 3 < 0 := by linarith
      have h8 : 1 / (x - 3) < a := by
        apply (div_lt_iff_of_neg' h7).mpr
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (a + 1 / 2)]
      exact h8
    rw [hB]
    exact h5