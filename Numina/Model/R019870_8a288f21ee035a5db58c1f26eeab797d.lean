import Mathlib

theorem algebra_3879 (k : ℤ) (y : ℝ → ℝ) (hy : y = fun x => 2 * x ^ 2 + 2 * x + 5)
    (h : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1 + y x1 = k ∧ x2 + y x2 = k) :
    k ≥ 4 := by
  rcases h with ⟨x1, x2, hx12, h1, h2⟩
  simp [hy] at h1 h2
  have eq1 : 2 * x1 ^ 2 + 3 * x1 + (5 - (k : ℝ)) = 0 := by
    nlinarith
  have eq2 : 2 * x2 ^ 2 + 3 * x2 + (5 - (k : ℝ)) = 0 := by
    nlinarith
  have h3 : (x1 - x2) * (2 * (x1 + x2) + 3) = 0 := by
    have eq1' : 2 * x1 ^ 2 + 3 * x1 + (5 - (k : ℝ)) = 0 := eq1
    have eq2' : 2 * x2 ^ 2 + 3 * x2 + (5 - (k : ℝ)) = 0 := eq2
    have eq3 : 2 * x1 ^ 2 + 3 * x1 + (5 - (k : ℝ)) - (2 * x2 ^ 2 + 3 * x2 + (5 - (k : ℝ))) = 0 := by
      linarith
    ring_nf at eq3 ⊢
    <;> nlinarith
  cases (mul_eq_zero.mp h3) with
  | inl h4 =>
    -- `h4` means $x1 - x2 = 0$ which contradicts the hypothesis.
    have h4 : x1 - x2 = 0 := h4
    have h5 : x1 = x2 := by linarith
    exfalso
    exact hx12 (by linarith)
  | inr h4 =>
    -- `h4` means $2 * (x1 + x2) + 3 = 0$
    -- `h5` means discriminant must be non-negative. The discriminant is $8k - 31$, so $8k - 31 \geq 0$.
    have h5 : (k : ℝ) ≥ (31 / 8 : ℝ) := by
      nlinarith [sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num), sq_pos_of_ne_zero (show (x1 - x2 : ℝ) ≠ 0 by
        intro h'
        apply hx12
        linarith
      ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 + 3 / 2)]
    have h6 : k ≥ 4 := by
      by_contra h7
      push_neg at h7
      have h8 : k ≤ 3 := by omega
      have h9 : (k : ℝ) ≤ (3 : ℝ) := by exact_mod_cast h8
      nlinarith
    exact_mod_cast h6