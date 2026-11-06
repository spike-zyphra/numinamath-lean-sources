import Mathlib

theorem algebra_93250 {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (h : ∀ k ∈ Finset.Icc 1 (n - 1), x (k + 1) = x k + 1 / 2) (hx1 : x 1 = 1) :
    ∑ i ∈ Finset.Icc 1 n, x i = (n ^ 2 + 3 * n) / 4 := by

  have h1 : ∀ (k : ℕ), k ≥ 1 → k ≤ n → x k = (k + 1 : ℝ) / 2 := by
    intro k hk1 hk2
    induction k with
    | zero =>
      linarith
    | succ k ih =>
      by_cases h2 : k = 0
      · -- Base case k = 1
        rw [h2]
        norm_num
        all_goals linarith [hx1]
      · -- Inductive step
        have hk3 : k ≥ 1 := by
          by_contra h4
          push_neg at h4
          have h5 : k = 0 := by linarith
          tauto
        have hk4 : k < n := by
          omega
        have hk6 : k ∈ Finset.Icc 1 (n - 1) := by
          simp at *
          omega
        have h2 := h k (hk6)
        have hk7 : x (k + 1) = x k + 1 / 2 := h2
        have hk8 : x k = (k + 1 : ℝ) / 2 := by
          apply ih
          all_goals
            omega
        rw [hk7, hk8]
        simp at *
        all_goals
          ring

  have h2 : ∀ (i : ℕ), i ∈ Finset.Icc 1 n → x i = (i + 1 : ℝ) / 2 := by
    intro i hi
    have h3 : i ≥ 1 := by
      have h4 : i ∈ Finset.Icc 1 n := hi
      simp at h4 ⊢
      omega
    have h4 : i ≤ n := by
      have h5 : i ∈ Finset.Icc 1 n := hi
      simp at h5 ⊢
      omega
    specialize h1 i (by linarith) (by linarith)
    simpa using h1

  have h3 : ∑ i in Finset.Icc 1 n, x i = ∑ i in Finset.Icc 1 n, ((i + 1 : ℝ) / 2) := by
    apply Finset.sum_congr
    · rfl
    · intro i hi
      specialize h2 i (show i ∈ Finset.Icc 1 n by simpa using hi)
      linarith

  rw [h3]

  have h4 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 n, ((i + 1 : ℝ) / 2) = (n ^ 2 + 3 * n) / 4 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      field_simp at *
      ring_nf at *

  specialize h4 n
  simpa using h4