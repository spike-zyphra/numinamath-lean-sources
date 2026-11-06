import Mathlib

open Finset

/- $6 \cdot 118 \quad x_{1}, x_{2}, \cdots, x_{1993}$ satisfy
$$
\begin{array}{l}
\left|x_{1}-x_{2}\right|+\left|x_{2}-x_{3}\right|+\cdots+\left|x_{1992}-x_{1993}\right|=1993, \\
y_{k}=\frac{x_{1}+x_{2}+\cdots+x_{k}}{k},(k=1,2, \cdots, 1993)
\end{array}
$$

Then what is the maximum possible value of $\left|y_{1}-y_{2}\right|+\left|y_{2}-y_{3}\right|+\cdots+\left|y_{1992}-y_{1993}\right|$? -/
theorem algebra_101384 :
    IsGreatest {s | ∃ x y : ℕ → ℝ,
      (∑ i ∈ range 1992, |x i - x (i + 1)| = 1993) ∧
      (∀ k ∈ range 1993, y k = (∑ i ∈ range (k + 1), x i) / (k + 1)) ∧
      s = ∑ i ∈ range 1992, |y i - y (i + 1)|} 1992 := by
  simp only [IsGreatest, mem_range, Set.mem_setOf_eq, upperBounds, and_imp]
  constructor
  -- Show that there exists a sequence x(i) such that ∑ i ∈ [0, 1992), |y(i) - y(i + 1)| = 1992.
  -- Take x(0) = 1993 and x(i) = 0 otherwise.
  -- Then y(i) = 1993 / (i + 1).
  · use fun i => if i = 0 then 1993 else 0, fun i => 1993 / (i + 1)
    constructorm* _ ∧ _
    · simp [sum_range_succ']
    · simp [sum_range_succ']
    · have eq : ∀ i : ℕ, |1993 / (i + 1 : ℝ) - 1993 / ((i + 1 : ℕ) + 1)| = (1993 / (i + 1) - 1993 / ((i + 1 : ℕ) + 1)) := by
        intro i
        rw [abs_of_nonneg]
        field_simp
        ring_nf
        positivity
      -- ∑ i ∈ [0, 1992), |1993 / (i + 1) - 1993 / (i + 2)|
      --   = 1993 / 1 - 1993 / (1991 + 2)
      --   = 1993 - 1 = 1992.
      simp_rw [eq, sum_range_sub']
      norm_num
  intro s ⟨x, y, hx, hy, hs⟩
  -- Assume that ∑ i ∈ [0, 1992), |x(i) - x(i + 1)| = 1993,
  -- y(k) = (∑ i ∈ [0, k], x(i)) / (k + 1), and show that
  -- ∑ k ∈ [0, 1992), |y(k) - y(k + 1)| ≤ 1992.
  subst s
  calc
    -- Show that
    -- |y(k) - y(k + 1)| ≤ ∑ i ∈ [0, k], (i + 1) / ((k + 1) * (k + 2)) * |x(i) - x(i + 1)|.
    ∑ k ∈ range 1992, |y k - y (k + 1)| ≤ ∑ k ∈ range 1992, ∑ i ∈ range (k + 1), (i + 1) / ((k + 1) * (k + 2)) * |x i - x (i + 1)| := by
      apply sum_le_sum
      simp only [mem_range]
      intro k hk
      calc
        --From the definition of y(k), we get
        -- |y(k) - y(k + 1)| = 1 / ((k + 1) * (k + 2)) * |∑ i ∈ [0, k], x i - x (k + 1)|.
        |y k - y (k + 1)| = 1 / ((k + 1) * (k + 2)) * |∑ i ∈ range (k + 1), (x i - x (k + 1))| := by
          rw [hy k (by linarith), hy (k + 1) (by linarith)]
          push_cast [show (k : ℝ) + 1 + 1 = k + 2 by ring]
          field_simp [abs_div, abs_of_nonneg]
          rw [sum_range_succ _ (k + 1)]
          ring_nf
        -- Show that |∑ i ∈ [0, k], x i - x (k + 1)| ≤ ∑ i ∈ [0, k], (i + 1) * |x(i) - x(i + 1)|.
        _ ≤ 1 / ((k + 1) * (k + 2)) * ∑ i ∈ range (k + 1), (i + 1) * |x i - x (i + 1)| := by
          clear * -
          gcongr
          -- It is enough to show that ∑ i ∈ [0, k], |x i - x (k + 1)| ≤ ∑ i ∈ [0, k], (i + 1) * |x(i) - x(i + 1)|.
          apply le_trans (abs_sum_le_sum_abs _ _)
          -- Proof by induction.
          induction k with
          -- For k = 0 everything is trivial.
          | zero => simp
          | succ k ih =>
            -- Consider k + 1.
            calc
              -- We have
              -- ∑ i ∈ [0, k + 1], |x i - x (k + 2)| = ∑ i ∈ [0, k], |x i - x (k + 2)| + |x (k + 1) - x (k + 2)|
              --      ≤ ∑ i ∈ [0, k], (|x i - x (k + 1)| + |x(k + 1) - x(k + 2)|) + |x(k + 1) - x(k + 2)|.
              ∑ i ∈ range (k + 1 + 1), |x i - x (k + 1 + 1)| = ∑ i ∈ range (k + 1), |x i - x (k + 2)| + |x (k + 1) - x (k + 2)| := by
                rw [sum_range_succ]
              _ ≤ ∑ i ∈ range (k + 1), |x i - x (k + 1)| + ∑ i ∈ range (k + 1), |x (k + 1) - x (k + 2)| + |x (k + 1) - x (k + 2)| := by
                rw [← sum_add_distrib]
                gcongr with i
                nth_rw 1 [show x i - x (k + 2) = x i - x (k + 1) + (x (k + 1) - x (k + 2)) by ring]
                apply abs_add_le
              -- From the induction hypothesis, we get
              -- ∑ i ∈ [0, k], |x i - x(k + 1)| ≤ ∑ i ∈ [0, k], (i + 1) * |x(i) - x(i + 1)|.
              _ ≤ ∑ i ∈ range (k + 1), (i + 1) * |x i - x (i + 1)| + (k + 2) * |x (k + 1) - x (k + 2)| := by
                rw [add_assoc]
                apply add_le_add ih
                simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
                ring_nf
                exact le_refl _
              -- We also have ∑ i ∈ [0, k], |x(k + 1) - x(k + 2)| + |x(k + 1) - x(k + 2)|
              --       = (k + 2) * |x(k + 1) - x(k + 2)|.
              -- And the result follows.
              _ = ∑ i ∈ range (k + 1 + 1), (i + 1) * |x i - x (i + 1)| := by
                rw [sum_range_succ _ (k + 1)]
                simp [show (k : ℝ) + 1 + 1 = k + 2 by ring]
        _ = ∑ i ∈ range (k + 1), (i + 1) / ((k + 1) * (k + 2)) * |x i - x (i + 1)| := by
          rw [mul_sum]
          apply sum_congr rfl
          intro i hi
          ring_nf
    -- Change the order of summation and get:
    -- ∑ k ∈ [0, 1992), |y(k) - y(k + 1)| ≤ ∑ k ∈ [0, 1992), ∑ i ∈ [0, k], (i + 1) / ((k + 1) * (k + 2)) * |x(i) - x(i + 1)|
    --          = ∑ i ∈ [0, 1992), ∑ k ∈ [i, 1992), (i + 1) / ((k + 1) * (k + 2)) * |x(i) - x(i + 1)|.
    _ = ∑ i ∈ range 1992, ∑ k ∈ Ico i 1992, (i + 1) / ((k + 1) * (k + 2)) * |x i - x (i + 1)| := by
      rw [range_eq_Ico, sum_Ico_Ico_comm]
    -- 1 / ((k + 1) * (k + 2)) = 1 / (k + 1) - 1 / (k + 2).
    _ = ∑ i ∈ range 1992, (i + 1) * |x i - x (i + 1)| * ∑ k ∈ Ico i 1992, ((1 : ℝ) / (k + 1 : ℕ) - 1 / (k + 1 + 1 : ℕ)) := by
      apply sum_congr rfl
      intro i hi
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      field_simp
      ring_nf
      simp
    -- ∑ k ∈ [i, 1992), (1 / (k + 1) - 1 / (k + 2)) = 1 / (i + 1) - 1 / 1993.
    _ = ∑ i ∈ range 1992, (i + 1) * |x i - x (i + 1)| * (1 / (i + 1) - 1 / 1993) := by
      apply sum_congr rfl
      intro i hi
      clear * - hi
      simp only [mem_range] at hi
      congr
      rw [sum_Ico_eq_sum_range]
      simp_rw [show ∀ k, i + k + 1 + 1 = i + (k + 1) + 1 by simp [add_assoc]]
      rw [sum_range_sub', show i + (1992 - i) + 1 = 1993 by omega]
      push_cast
      ring
    -- (i + 1) * (1 / (i + 1) - 1 / 1993) ≤ 1 - 1 / 1993.
    _ ≤ ∑ i ∈ range 1992, |x i - x (i + 1)| * (1 - 1 / 1993) := by
      apply sum_le_sum
      intro i hi
      rw [mul_right_comm, mul_sub]
      field_simp
      rw [mul_comm]
      clear * -
      gcongr
      linarith
    -- We get ∑ i ∈ [0, 1992), |x(i) - x(i + 1)| * (1 - 1 / 1993)
    --          = 1993 * (1 - 1 / 1993)
    --          = 1992.
    _ = 1993 * (1 - 1 / 1993) := by simp [← sum_mul, hx]
    -- We conclude that ∑ k ∈ [0, 1992), |y(k) - y(k + 1)| ≤ 1992.
    _ = 1992 := by norm_num