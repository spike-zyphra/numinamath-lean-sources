import Mathlib

open Real

theorem inequalities_99351 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    (∑ i : Fin n, a i) ^ 2 ≤ n * ∑ i : Fin n, (a i) ^ 2 ∧
    ∀ x ∈ Set.Icc (3 / 2) 5, 2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) < 2 * sqrt 19 := by
  constructor
  · -- Proof of (1): $\left(a_{1}+a_{2}+\cdots+a_{n}\right)^{2} \leqslant n\left(a_{1}^{2}+a_{2}^{2}+\cdots+a_{n}^{2}\right)$
    have h1 : (∑ i : Fin n, a i) ^ 2 ≤ n * ∑ i : Fin n, (a i) ^ 2 := by
      have h2 : (∑ i : Fin n, a i) ^ 2 = (∑ i : Fin n, (a i : ℝ) * (1 : ℝ)) ^ 2 := by
        simp
      rw [h2]
      have h3 : (∑ i : Fin n, (a i : ℝ) * (1 : ℝ)) ^ 2 ≤ (∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (1 : ℝ) ^ 2) := by
        apply Finset.sum_mul_sq_le_sq_mul_sq
      have h4 : ∑ i : Fin n, (1 : ℝ) ^ 2 = (n : ℝ) := by
        simp
      rw [h4] at h3
      nlinarith
    exact h1
  · -- Proof of (2): If $\frac{3}{2} \leqslant x \leqslant 5$, then $2 \sqrt{x+1}+\sqrt{2 x-3}+\sqrt{15-3 x}<2 \sqrt{19}$.
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have h1 : 0 ≤ x + 1 := by
      nlinarith
    have h2 : 0 ≤ 2 * x - 3 := by
      nlinarith
    have h3 : 0 ≤ 15 - 3 * x := by
      nlinarith
    have h4 : (2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x)) ^ 2 < (76 : ℝ) := by
      nlinarith [sq_nonneg (sqrt (x + 1) - sqrt (2 * x - 3)), sq_nonneg (sqrt (x + 1) - sqrt (15 - 3 * x)), sq_nonneg (sqrt (2 * x - 3) - sqrt (15 - 3 * x)),
        Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x),
        Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 3 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 15 - 3 * x by linarith),
        mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (2 * x - 3)), mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (15 - 3 * x)), mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg (15 - 3 * x)),
        sq_nonneg (x - 3), Real.sqrt_nonneg 19, Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num)
      ]
    have h5 : 2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) < 2 * sqrt 19 := by
      have h6 : (2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x)) ^ 2 < (76 : ℝ) := h4
      have h7 : (2 * sqrt 19) ^ 2 = 76 := by
        calc
          (2 * sqrt 19) ^ 2 = 4 * (sqrt 19) ^ 2 := by ring
          _ = 4 * 19 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19)]
          _ = (76 : ℝ) := by norm_num
      have h8 : 0 ≤ (2 * sqrt 19 : ℝ) := by
        positivity
      have h9 : (2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) : ℝ) < (2 * sqrt 19 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (19 : ℝ), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x)]
      linarith
    exact h5