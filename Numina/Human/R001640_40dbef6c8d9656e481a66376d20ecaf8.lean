import Mathlib

open Real Set Finset
open scoped BigOperators

/- 3. (CZS 4) Let $x_{1}, x_{2}, \ldots, x_{n}$ be real numbers satisfying $x_{1}+x_{2}+\cdots+x_{n}=$ 0 . Let $m$ be the least and $M$ the greatest among them. Prove that  $$ x_{1}^{2}+x_{2}^{2}+\cdots+x_{n}^{2} \leq-n m M $$ -/
theorem inequalities_24941 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
  (hsum : ∑ i : Fin n, x i = 0) (m M : ℝ)
  (hm : ∃ i : Fin n, x i = m) (hM : ∃ i : Fin n, x i = M)
  (hmub : ∀ i : Fin n, x i ≥ m) (hMub : ∀ i : Fin n, x i ≤ M) :
  ∑ i : Fin n, (x i)^2 ≤ -n * m * M := by 
  have h1 : ∀ i : Fin n, (M - x i) * (m - x i) ≤ 0 := by 
    intro i
    obtain aux1 := hmub i
    obtain aux2 := hMub i
    have aux3 : (M - x i) ≥ 0 := by linarith
    have aux4 : (m - x i) ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos aux3 aux4
  have ineq1 : 0 ≥ ∑ i : Fin n, (M - x i) * (m - x i) := by 
    calc 
      _ = ∑ i : Fin n, 0 := by 
        simp
      _ ≥ ∑ i : Fin n, (M - x i) * (m - x i) := by 
        apply Finset.sum_le_sum
        intro i hi
        exact h1 i
  have ineq2 : ∑ i : Fin n, (M - x i) * (m - x i)  = n * m * M - 
    (m + M) * (∑ i : Fin n, x i) + (∑ i : Fin n, (x i ^ 2)) := by 
      calc 
        _ = ∑ i : Fin n, (m * M - (m + M) * x i + x i ^ 2) := by 
          apply sum_congr
          simp
          intro i hi
          ring
        _ = (∑ i : Fin n, m * M) - (∑ i : Fin n, (m + M) * x i)
          + (∑ i : Fin n, (x i ^ 2))  := by 
          rw [sum_add_distrib, sum_sub_distrib]
        _ = _ := by 
          simp
          rw [mul_sum]
          norm_num
          ring
  -- since ∑ i : Fin n, x i = 0, and we rewrite hsum in ineq2 
  rw [hsum] at ineq2 
  simp at ineq2
  have ineq3 : 0 ≥ ↑n * m * M + ∑ i : Fin n, x i ^ 2 := by 
    linarith
  linarith