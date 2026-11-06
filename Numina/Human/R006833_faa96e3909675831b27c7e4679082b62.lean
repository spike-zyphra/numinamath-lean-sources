import Mathlib

/-Let $N_0$ be a positive integer. Suppose there exist $r$ unique nonnegative integers $n_1 > n_2 > \dots > n_r$ and $r$ integers $a_k$ ($1\le k\le r$) with each $a_k$ either $1$ or $-1$ such that $\sum_{k=1}^{r} a_k3^{n_k} = N_0$.
If $N_0=5$, find $n_1 + n_2 + \dots + n_r$. Show the answer is 3.-/
theorem number_theory_641586 :
    ∃ (r : ℕ) (n : Fin r → ℕ) (a : Fin r → ℤ),
      (∀ k : Fin r, a k = 1 ∨ a k = -1) ∧
      (∀ k l : Fin r, k.val < l.val → n k > n l) ∧
      (∀ k : Fin r, n k ≥ 0) ∧
      (∑ k : Fin r, (a k * 3 ^ (n k)) = 5) ∧
      (∑ k : Fin r, n k = 3) := by
  -- Construct $r = 3$, $n$, $a$ based on modulo steps.
  use 3
  let n : Fin 3 → ℕ := Matrix.vecCons 2 (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty))
  let a : Fin 3 → ℤ := Matrix.vecCons 1 (Matrix.vecCons (-1) (Matrix.vecCons (-1) Matrix.vecEmpty))
  -- Prove all conditions.
  refine ⟨n, a, ?_⟩
  -- Condition $1$: $a k = 1$ or $a k = -1$.
  have h_a_valid : ∀ k : Fin 3, a k = 1 ∨ a k = -1 := by
    intro k
    fin_cases k
    · simp [a, Matrix.vecCons]
    · simp [a, Matrix.vecCons]
    · simp [a, Matrix.vecCons]; right; rfl
  -- Condition $2$: $∀ k l$, $k.val < l.val$ → $n k > n l$.
  have h_n_decreasing : ∀ k l : Fin 3, k.val < l.val → n k > n l := by
    intro k l h_kl
    fin_cases k
    · fin_cases l
      · contradiction
      · have h_n0 : n 0 = 2 := rfl
        have h_n1 : n 1 = 1 := rfl
        simp
        rw [h_n0, h_n1]
        norm_num
      · have h_n0 : n 0 = 2 := rfl
        have h_n2 : n 2 = 0 := rfl
        simp
        rw [h_n0, h_n2]
        norm_num
    · fin_cases l
      · contradiction
      · contradiction
      · have h_n1 : n 1 = 1 := rfl
        have h_n2 : n 2 = 0 := rfl
        simp
        rw [h_n1, h_n2]
        norm_num
    · fin_cases l
      · contradiction
      · contradiction
      · have h_n1 : n 1 = 1 := rfl
        have h_n2 : n 2 = 0 := rfl
        simp
        contradiction
  -- Condition $3$: $n k ≥ 0$.
  have h_n_nonneg : ∀ k : Fin 3, n k ≥ 0 := by
    intro k
    fin_cases k
    · simp [n, Matrix.vecCons]
    · simp [n, Matrix.vecCons]
    · simp [n, Matrix.vecCons]
  -- Condition $4$: $∑ (a k * 3 ^ (n k)) = 5$.
  have h_sum_eq_5 : ∑ k : Fin 3, (a k * 3 ^ (n k)) = 5 := by tauto
  -- Condition $5$: $∑ n k = 3$.
  have h_sum_n_eq_3 : ∑ k : Fin 3, n k = 3 := by
    simp [Fin.sum_univ_succ, n, Matrix.vecCons]
  -- Combine all conditions.
  exact And.intro h_a_valid (And.intro h_n_decreasing (And.intro h_n_nonneg (And.intro h_sum_eq_5 h_sum_n_eq_3)))
