import Mathlib

open Real

/- Let $x_{1}, x_{2}, \ldots, x_{n}$ be real numbers satisfying $\sum_{k=1}^{n-1} \min \left(x_{k} ; x_{k+1}\right)=\min \left(x_{1}, x_{n}\right)$.

Prove that $\sum_{k=2}^{n-1} x_{k} \geq 0$. -/
theorem inequalities_605844 {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ)
    (h : ∑ k ∈ Finset.Icc 1 (n - 1), min (x k) (x (k + 1)) = min (x 1) (x n)) :
    ∑ k ∈ Finset.Icc 2 (n - 1), x k ≥ 0 := by
  by_cases hn' : n ≤ 1
  · simp [hn']
  · push_neg at hn'
    -- Case I. If $\min \left(x_{1}, x_{n}\right)=x_{1}$
    by_cases hmin : x n ≥ x 1
    · have h : x 1 ≤ ∑ k ∈ Finset.Icc 1 (n - 1), x k := by
        calc
          x 1 = min (x 1) (x n) := by exact Eq.symm (min_eq_left hmin)
          _ = ∑ k ∈  Finset.Icc 1 (n - 1), min (x k) (x (k + 1)) := by rw [h]
          _ ≤ ∑ k ∈  Finset.Icc 1 (n - 1), x k := by
            --  we know that $x_{k} \geq \min \left(x_{k} ; x_{k+1}\right)$ for all $k \in{1,2,3, \ldots, n-1}$.
            apply Finset.sum_le_sum
            simp [min_le_left]
      -- So $x_{1}+x_{2}+\ldots+x_{n-1} \geq \sum_{k=1}^{n-1} \min \left(x_{k} ; x_{k+1}\right)=\min \left(x_{1}, x_{n}\right)=x_{1}$,
      rw [Finset.Icc_eq_cons_Ioc ((Nat.le_sub_one_iff_lt hn).mpr hn'), Finset.sum_cons] at h
      simpa using h

    · push_neg at hmin
      -- Case II. If $\min \left(x_{1}, x_{n}\right)=x_{n}$,
      have h : x n ≤ ∑ k ∈ Finset.Icc 1 (n - 1), x (k + 1) := by
        calc
          x n = min (x 1) (x n) := by exact Eq.symm (min_eq_right_of_lt hmin)
          _ = ∑ k ∈ Finset.Icc 1 (n - 1), min (x k) (x (k + 1)) := by rw [h]
          _ ≤ ∑ k ∈ Finset.Icc 1 (n - 1), x (k + 1) := by
            --  we know that $x_{k} \geq \min \left(x_{k-1} ; x_{k}\right)$ for all $k \in{2,3,4, \ldots, n}$.
            apply Finset.sum_le_sum
            simp [min_le_right]
      --  So $x_{2}+x_{3}+\ldots+x_{n} \geq \sum_{k=1}^{n-1} \min \left(x_{k} ; x_{k+1}\right)=\min \left(x_{1}, x_{n}\right)=x_{n}$,
      rw [Finset.Icc_eq_cons_Ico ((Nat.le_sub_one_iff_lt hn).mpr hn'),
      Finset.sum_cons, Nat.sub_add_cancel (by linarith)] at h
      simp only [le_add_iff_nonneg_right] at h

      apply h.trans (le_of_eq ?_)

      have : Finset.Icc 2 (n - 1) = Finset.Ico 2 n := rfl
      have h1: 2 = 1+1 := by norm_num
      have h2: n = n-1 + 1 := by omega
      rw [this, h1]
      nth_rw 2 [h2]
      rw [← Finset.sum_Ico_add]
      simp only [add_comm]