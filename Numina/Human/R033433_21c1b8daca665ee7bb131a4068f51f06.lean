import Mathlib

open Finset Real

/- Example 3 Let $a_{1}, a_{2}, \cdots, a_{n}$ all be positive numbers, prove that:

$$

\frac{a_{2}}{\left(a_{1}+a_{2}\right)^{2}}+\frac{a_{3}}{\left(a_{1}+a_{2}+a_{3}\right)^{2}}+\cdots+\frac{a_{n}}{\left(a_{1}+a_{2}+\cdots+a_{n}\right)^{2}}<\frac{1}{a_{1}} .

$$
 -/
theorem inequalities_281067 {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Icc 1 n, 0 < a i) :
    ∑ i ∈ Icc 2 n, a i / (∑ j ∈ Icc 1 i, a j) ^ 2 < 1 / a 1 := by
  -- Define d(i) = ∑ j ∈ [1, i], a(j).
  set d : ℕ → ℝ := fun i => ∑ j ∈ Icc 1 i, a j
  -- Show that d(i) > 0 for all i ∈ [1, n].
  have hd_pos {i} (hi1 : 1 ≤ i) (hi2 : i ≤ n) : 0 < d i := by
    apply sum_pos
    · intro j
      simp only [mem_Icc, and_imp] at ha ⊢
      intro hj1 hj2
      apply ha j hj1 (by linarith)
    · simp only [nonempty_Icc, hi1]
  -- Show that d(i) = a(i) + d(i - 1) for i ∈ [2, n].
  have hd_pred {i} (hi1 : 2 ≤ i) (hi2 : i ≤ n) : d i = a i + d (i - 1) := by
    simp [d]
    nth_rw 1 [show i = (i - 1) + 1 by omega, sum_Icc_succ_top (by omega), add_comm]
    congr
    omega
  -- Consider two cases n = 1 or 2 ≤ n.
  cases' show n = 1 ∨ 2 ≤ n by omega with hn hn
  -- If n = 1 then the result follows from 0 < 1 / a(1).
  · simp [hn, ha]
  calc
    -- ∑ i ∈ [2, n], a i / (∑ j ∈ [1, i], a j) ^ 2 = ∑ i ∈ [2, n], a i / (d i * d i).
    ∑ i ∈ Icc 2 n, a i / (∑ j ∈ Icc 1 i, a j) ^ 2 = ∑ i ∈ Icc 2 n, a i / (d i * d i) := by
        simp_rw [d, pow_two]
    -- We have a(i) / (d(i) * d(i)) ≤ a(i) / (d(i - 1) * d(i)) (because d(i - 1) ≤ d(i))
    --                              = 1 / d(i - 1) - 1 / d(i) (because d(i) - d(i - 1) = a(i)).
    _ ≤ ∑ i ∈ Icc 2 n,  (1 / d (i - 1) - 1 / d i) := by
        apply sum_le_sum
        simp only [mem_Icc, and_imp]
        intro i hi1 hi2
        rw [div_sub_div _ _ _ (ne_of_gt <| hd_pos (by omega) hi2)]
        swap
        · apply ne_of_gt <| hd_pos (by omega) (by omega)
        nth_rw 3 [hd_pred hi1 hi2]
        rw [show 1 * (a i + d (i - 1)) - d (i - 1) * 1 = a i by ring]
        gcongr
        · apply le_of_lt
          apply ha
          simp only [mem_Icc]
          constructor <;> omega
        · apply mul_pos <;> apply hd_pos <;> omega
        · apply le_of_lt
          apply hd_pos (by omega) hi2
        · simp [← sub_nonneg, hd_pred hi1 hi2]
          rw [sub_zero]
          apply le_of_lt
          apply ha
          simp only [mem_Icc]
          constructor <;> omega
    _ = ∑ i ∈ Ico 2 (n + 1), (1 / d (i - 1) - 1 / d i) := rfl
    -- ∑ i ∈ [2, n], (1 / d(i - 1) - 1 / d(i)) = ∑ i ∈ [0, n - 1), (1 / d(i + 1) - 1 / d(i + 2)).
    _ = ∑ i ∈ range (n - 1), (1 / d (i + 1) - 1 / d (i + 1 + 1)) := by
        rw [sum_Ico_eq_sum_range, show n + 1 - 2 = n - 1 by omega]
        apply sum_congr rfl
        intro i hi
        rw [show 2 + i - 1 = i + 1 by omega, show i + 1 + 1 = 2 + i by linarith]
    -- ∑ i ∈ [0, n - 1), (1 / d(i + 1) - 1 / d(i + 2)) = 1 / d(1) - 1 / d(n) = 1 / a(1) - 1 / d(n).
    _ = 1 / a 1 - 1 / d n := by
        rw [sum_range_sub', show n - 1 + 1 = n by omega, zero_add]
        congr
        simp [d]
    -- 1 / a(1) - 1 / d(n) < 1 / a(1) because 1 / d(n) > 0.
    _ < 1 / a 1 - 0 := by
        gcongr
        field_simp
        exact hd_pos (by omega) (le_refl _)
    _ = 1 / a 1 := by simp