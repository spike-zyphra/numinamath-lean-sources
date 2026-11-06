import Mathlib

open Finset

/- Let's prove that for any positive integers $a_{1}, \ldots, a_{n}$,
$$
a_{1}+\frac{2}{\frac{1}{a_{1}}+\frac{1}{a_{2}}}+\frac{3}{\frac{1}{a_{1}}+\frac{1}{a_{2}}+\frac{1}{a_{3}}}+\cdots+\frac{n}{\frac{1}{a_{1}}+\frac{1}{a_{2}}+\cdots+\frac{1}{a_{n}}}<2\left(a_{1}+a_{2}+\cdots+a_{n}\right)

$$
 -/
theorem inequalities_210843 (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) :
    ∑ i ∈ Icc 1 n, i / (∑ j ∈ Icc 1 i, 1 / a j) < 2 * ∑ i ∈ Icc 1 n, a i := by
  -- Prove a lemma missing in Mathlib 4.15:
  -- ∑ i ∈ [m, n), (f (i + 1) - f i) = f n - f m.
  have sum_Ico_sub {m n : ℕ} (f : ℕ → ℝ) (hmn : m ≤ n) : ∑ i ∈ Ico m n, (f (i + 1) - f i) = f n - f m := by
    rw [sum_Ico_eq_sub _ hmn, sum_range_sub, sum_range_sub]
    ring
  -- Prove the following inequality:
  -- (∑ i ∈ [1, k], i) / (∑ i ∈ [1, k], 1 / a i) ≤ (∑ i ∈ [1, k], i ^ 2 * a i) / (k * (k + 1) / 2).
  have h1 {k : ℕ} (hk : 1 ≤ k) : (∑ i ∈ Icc (1 : ℕ) k, i : ℝ) / ∑ i ∈ Icc (1 : ℕ) k, (1 : ℝ) / a i
      ≤ (∑ i ∈ Icc (1 : ℕ) k, i ^ 2 * a i) / (k * (k + 1) / 2) := by
    -- Define w(i) = i and z(i) = i * a(i).
    set w : Icc (1 : ℕ) k → ℝ := fun i => i
    set z : Icc (1 : ℕ) k → ℝ := fun i => i * a i
    -- We have 0 < w(i) for all i ∈ [1, k].
    have hw : ∀ i ∈ univ, 0 < w i := by
      simp only [univ_eq_attach, mem_attach, forall_const, Subtype.forall, mem_Icc, w]
      intro i hi
      norm_cast
      linarith
    -- We have 0 < z(i) for all i ∈ [1, k].
    have hz : ∀ i ∈ univ, 0 < z i := by
      simp only [univ_eq_attach, mem_attach, forall_const, Subtype.forall, mem_Icc, and_imp, z]
      intro i hi1 hi2
      exact mul_pos (by norm_cast) (ha i)
    -- The set [1, k] is not empty.
    have hne : (univ : Finset (Icc (1 : ℕ) k)).Nonempty := by
      simp only [univ_eq_attach, attach_nonempty_iff, nonempty_Icc, hk]
    calc
      -- We have
      -- (∑ i ∈ [1, k], i) / (∑ i ∈ [1, k], 1 / a i) = (∑ i, w i) / ∑ i, w i / z i.
      (∑ i ∈ Icc (1 : ℕ) k, i : ℝ) / ∑ i ∈ Icc (1 : ℕ) k, (1 : ℝ) / a i = (∑ i, w i) / ∑ i, w i / z i := by
        congr 1
        · rw [univ_eq_attach, sum_attach]
        · rw [univ_eq_attach, ← sum_attach]
          apply sum_congr rfl
          simp only [mem_attach, mul_one, forall_const, Subtype.forall, mem_Icc, and_imp, w, z]
          intro i hi1 hi2
          rw [div_mul_cancel_left₀, one_div]
          norm_cast
          linarith
      -- Apply HM-GM inequality and get
      -- (∑ i, w i) / ∑ i, w i / z i ≤ (∏ i, z i ^ w i) ^ (∑ i, w i)⁻¹.
      _ ≤ (∏ i, z i ^ w i) ^ (∑ i, w i)⁻¹ := Real.harm_mean_le_geom_mean _ hne w z hw (sum_pos hw hne) hz
      -- Apply GM-AM inequality and get
      -- (∏ i, z i ^ w i) ^ (∑ i, w i)⁻¹ ≤ (∑ i, w i * z i) / ∑ i, w i.
      _ ≤ (∑ i, w i * z i) / ∑ i, w i := by
        apply Real.geom_mean_le_arith_mean
        · intro i hi
          exact le_of_lt (hw i hi)
        · exact sum_pos hw hne
        · intro i hi
          exact le_of_lt (hz i hi)
      -- It is left to show that
      -- (∑ i, w i * z i) / ∑ i, w i = (∑ i ∈ [1, k], i^2 * a(i)) / (k * (k + 1) / 2).
      _ = (∑ i ∈ Icc (1 : ℕ) k, i ^ 2 * a i) / (k * (k + 1) / 2) := by
          congr 1
          · symm
            rw [univ_eq_attach, ← sum_attach]
            apply sum_congr rfl
            simp only [mem_attach, forall_const, Subtype.forall, mem_Icc, w, z]
            intro i hi
            group
          · rw [univ_eq_attach, sum_attach]
            field_simp
            calc
              (∑ i ∈ Icc (1 : ℕ) k, (i : ℝ)) * 2 = (((∑ i ∈ range (k + 1), i) * 2 : ℕ) : ℝ) := by
                simp [sum_range_eq_add_Ico]
                rfl
              _ = (k : ℝ) * (k + 1) := by
                rw [sum_range_id_mul_two, add_tsub_cancel_right]
                push_cast
                group
  -- Prove the following inequality:
  -- k / ∑ j ∈ [1, j], 1 / a(j) ≤ 4 / (k * (k + 1)^2) * ∑ j ∈ [1, k], j^2 * a(j).
  have hineq {k : ℕ} (hk : 1 ≤ k) : k / ∑ j ∈ Icc 1 k, 1 / a j ≤ 4 / (k * (k + 1)^2) * ∑ j ∈ Icc 1 k, j^2 * a j := calc
    -- We have
    -- k / ∑ j ∈ [1, j], 1 / a(j) = ((∑ j ∈ [0, k + 1), j) * 2) / (k + 1) / ∑ j ∈ [1, k], 1 / a(j).
    -- This equality follows from (∑ j ∈ [0, k + 1), j) * 2 = k * (k + 1).
    k / ∑ j ∈ Icc 1 k, 1 / a j = (((∑ j ∈ range (k + 1), j) * 2 : ℕ) / (k + 1)) / ∑ j ∈ Icc 1 k, 1 / a j := by
      rw [sum_range_id_mul_two, add_tsub_cancel_right]
      field_simp
    -- ((∑ j ∈ [0, k + 1), j) * 2) / (k + 1) / ∑ j ∈ [1, k], 1 / a(j)
    --    = 2 / (k + 1) * ((∑ j ∈ [1, k], j) / ∑ j ∈ [1, k], 1 / a j)
    --    ≤ 2 / (k + 1) * ((∑ j ∈ [1, k], j^2 * a j) / (k * (k + 1) / 2) (from h1)
    --    = 4 / (k * (k + 1)^2) * ∑ j ∈ [1, k], j^2 * a j.
    _ = (2 / (k + 1)) * ((∑ j ∈ Icc 1 k, j) / ∑ j ∈ Icc 1 k, 1 / a j) := by
      push_cast
      suffices ∑ j ∈ range (k + 1), j = ∑ j ∈ Icc 1 k, j by
        rify at this
        rw [this]
        ring
      rw [sum_range_eq_add_Ico _ (by linarith), zero_add]
      rfl
    _ ≤ (2 / (k + 1)) * ((∑ j ∈ Icc (1 : ℕ) k, j ^ 2 * a j) / (k * (k + 1) / 2)) := by
      push_cast
      gcongr (2 / (k + 1)) * ?_
      exact h1 hk
    _ = 4 / (k * (k + 1)^2) * ∑ j ∈ Icc 1 k, j^2 * a j := by
      field_simp
      ring
  calc
    -- We have
    -- ∑ i ∈ [1, n], i / ∑ j ∈ [1, i], 1 / a j
    --    ≤ ∑ i ∈ [1, n], 4 / (i * (i + 1)^2) * ∑ j ∈ [1, i], j^2 * a j (from hineq)
    --    = ∑ j ∈ [1, n], (∑ i ∈ [j, n], 4 / (i * (i + 1)^2)) * j^2 * a j
    ∑ i ∈ Icc 1 n, i / ∑ j ∈ Icc 1 i, 1 / a j ≤ ∑ i ∈ Icc 1 n, 4 / (i * (i + 1)^2) * ∑ j ∈ Icc 1 i, j^2 * a j := by
      apply sum_le_sum
      intro i hi
      simp only [mem_Icc] at hi
      exact hineq hi.1
    _ = ∑ i ∈ Ico 1 (n + 1), ∑ j ∈ Ico 1 (i + 1), 4 / (i * (i + 1)^2) * (j^2 * a j) := by
      simp_rw [mul_sum]
      rfl
    _ = ∑ j ∈ Icc 1 n, (∑ i ∈ Icc j n, (4 : ℝ) / (i * (i + 1)^2)) * j^2 * a j := by
      rw [← sum_Ico_Ico_comm]
      simp_rw [sum_mul, mul_assoc]
      rfl
    -- Show that 4 / (i * (i + 1)^2) ≤ (4 * i + 2) / (i^2 + (i + 1)^2) for all i ∈ [1, n].
    _ ≤ ∑ j ∈ Icc 1 n, (∑ i ∈ Icc j n, (4 * i + 2 : ℝ) / (i^2 * (i + 1)^2)) * j^2 * a j := by
      apply sum_le_sum
      intro i hi
      gcongr ?_ * i^2 * a i
      · exact le_of_lt (ha i)
      apply sum_le_sum
      intro k hk
      simp only [mem_Icc] at hk hi
      rw [div_le_div_iff₀]
      · rw [← sub_nonneg]
        ring_nf
        positivity
      · norm_cast
        apply mul_pos (by linarith) (by positivity)
      · norm_cast
        apply mul_pos (by nlinarith) (by positivity)
    -- We have
    -- (4 * i + 2) / (i^2 * (i + 1)^2) = 2 / i^2 - 2 / (i + 1)^2.
    -- So ∑ i ∈ [j, n], (4 * i + 2) / (i^2 * (i + 1)^2) = 2 / j^2 - 2 / (n + 1)^2.
    _ = ∑ j ∈ Icc 1 n, ((2 : ℝ) / j^2 - 2 / (n + 1)^2) * j^2 * a j := by
      apply sum_congr rfl
      intro k hk
      congr
      calc
        ∑ i ∈ Icc k n, (4 * i + 2 : ℝ) / (i ^ 2 * (i + 1) ^ 2) = -∑ i ∈ Ico k (n + 1), ((2 : ℝ) / (i + 1 : ℕ)^2 - 2 / i^2) := by
          rw [← sum_neg_distrib]
          apply sum_congr rfl
          intro i hi
          have hi0 : (i : ℝ) ≠ 0 := by
            norm_cast
            simp only [mem_Icc] at hi hk
            linarith
          field_simp [hi0]
          ring
        _ = (2 : ℝ) / k^2 - 2 / (n + 1)^2 := by
          rw [sum_Ico_sub (f := fun i => (2 : ℝ) / i^2)]
          · push_cast
            ring
          · simp only [mem_Icc] at hk
            linarith
    -- We have
    -- (2 / j^2 - 2 / (n + 1)^2) * j^2 * a j = (2 - 2 * j^2 / (n + 1)^2) * a j < 2 * a j.
    _ < 2 * ∑ i ∈ Icc 1 n, a i := by
      rw [mul_sum]
      have h {k : ℕ} (hk : k ∈ Icc 1 n) : ((2 : ℝ) / k^2 - 2 / (n + 1)^2) * k^2 * a k < 2 * a k := by
        rw [sub_mul, mul_lt_mul_right (ha k)]
        have hk0 : 0 < k := by
          simp only [mem_Icc] at hk
          linarith
        rw [div_mul_cancel₀ _ (by norm_cast; nlinarith), sub_lt_self_iff]
        positivity
      apply sum_lt_sum
      · intro k hk
        exact le_of_lt (h hk)
      · use 1
        refine ⟨by simp; linarith, ?_⟩
        apply h
        simp
        linarith