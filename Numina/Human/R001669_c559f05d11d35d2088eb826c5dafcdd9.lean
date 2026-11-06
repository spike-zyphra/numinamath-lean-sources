import Mathlib

/- 7. (GDR) Prove that from $x+y=1(x, y \in \mathbb{R})$ it follows that
$$ x^{m+1} \sum_{j=0}^{n}\binom{m+j}{j} y^{j}+y^{n+1} \sum_{i=0}^{m}\binom{n+i}{i} x^{i}=1 \quad(m, n=0,1,2, \ldots) . $$ -/
theorem algebra_25070 {x y : ℝ} (h : x + y = 1) (m n : ℕ) (S : ℕ → ℝ)
    (hS: ∀ m : ℕ, S m = x ^ (m + 1) * ∑ j ∈ Finset.range (n + 1), (m + j).choose j * y ^ j
    + y ^ (n + 1) * ∑ i ∈ Finset.range (m + 1), (n + i).choose i * x ^ i):
    S m = 1 := by

    induction' m with m ih
    . -- case m = 0, direct computation.
      simp [hS, show x = 1 - y by simp [←h], mul_comm, geom_sum_mul_neg y (n + 1)]
    . -- case m = m + 1, direct computation.
      suffices S (m + 1) - S m = 0 by linarith
      calc
        _ = x ^ (m + 2) * ∑ j ∈ Finset.range (n + 1), (m + 1 + j).choose j * y ^ j
          - x ^ (m + 1) * ∑ j ∈ Finset.range (n + 1), (m + j).choose j * y ^ j
          + (y ^ (n + 1) * ∑ i ∈ Finset.range (m + 2), (n + i).choose i * x ^ i
          - y ^ (n + 1) * ∑ i ∈ Finset.range (m + 1), (n + i).choose i * x ^ i) := by rw [hS, hS]; ring
        _ = x ^ (m + 1) * (∑ j ∈ Finset.range (n + 1), ((m + 1 + j).choose j * y ^ j * x - (m + j).choose j * y ^j))
          + y ^ (n + 1) * x ^ (m + 1) * (n + m + 1).choose (m + 1):= by
          rw [pow_succ, mul_assoc, Finset.mul_sum]
          rw [←mul_sub, ←Finset.sum_sub_distrib]
          simp [←mul_sub, Finset.sum_range_succ _ (m + 1)]
          rw [←mul_comm (x ^ (m + 1)) ↑((n + (m + 1)).choose (m + 1))]
          rw [←mul_assoc _ (x ^ (m + 1)) ↑((n + (m + 1)).choose (m + 1))]
          simp [←add_assoc n m 1]
          left; congr; ext; ring
        _ = x ^ (m + 1) * (∑ j ∈ Finset.range (n + 1), y ^ j * ((m + 1 + j).choose j - (m + j).choose j - ((m + 1 + j).choose j) * y)
        + y ^ (n + 1) * (m + n + 1).choose (m + 1)) := by
          rw [mul_comm (y ^ (n + 1)) (x ^ (m + 1))]
          rw [mul_assoc (x ^ (m + 1))]
          rw [←mul_add (x ^ (m + 1))]
          nth_rewrite 2 [show x = 1 - y by simp [←h]]
          congr 5; ext; ring; ring

      suffices ∑ j ∈ Finset.range (n + 1), y ^ j * (↑((m + 1 + j).choose j) - ↑((m + j).choose j) - ↑((m + 1 + j).choose j) * y) + y ^ (n + 1) * ↑((m + n + 1).choose (m + 1)) = 0 by
        simp [this]
      calc
        _ = ∑ j ∈ Finset.range n, y ^ (j + 1) * (↑((m + j + 2).choose (j + 1)) - ↑((m + j + 1).choose (j + 1)) - ↑((m + j + 2).choose (j + 1)) * y)
        - y + y ^ (n + 1) * ↑((m + n + 1).choose (m + 1)) := by
          congr
          rw [Finset.sum_range_succ']
          congr
          . ext j
            ring_nf
          . simp
        _ = ∑ j ∈ Finset.range n, (y ^ (j + 1) * (m + j + 1).choose j
          - y ^ (j + 2) * (m + j + 2).choose (j + 1))
          - y + y ^ (n + 1) * ↑((m + n + 1).choose (m + 1)):= by
          congr; ext j
          simp [Nat.choose_succ_succ' (m + j + 1) j]; ring
        _ = 0 := by
          conv =>
            enter [1, 1, 1, 2]; ext j
            rw [show j + 2 = j + 1 + 1 by rfl, show m + j + 2 = m + (j + 1) + 1 by rfl]
          rw [Finset.sum_range_sub']
          have : (m + n + 1).choose n = (m + n + 1).choose (m + 1) := by
            apply Nat.choose_symm_of_eq_add; linarith
          simp [this]

