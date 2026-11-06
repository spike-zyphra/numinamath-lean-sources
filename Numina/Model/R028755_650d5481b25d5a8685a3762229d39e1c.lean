import Mathlib

open Real

theorem inequalities_257503 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∑ i : Fin n, a i = 1) (ha' : ∀ i : Fin n, 0 < a i) :
    ∑ i : Fin n, ∑ j : Fin n, (a i) * (a j) / (a i + a j) ≤ n / 2 := by 
  have h1 : ∀ i j : Fin n, (a i) * (a j) / (a i + a j) ≤ (a i + a j) / 4 := by
    intro i j
    have h1 : 0 < a i := ha' i
    have h2 : 0 < a j := ha' j
    have h3 : 0 < a i + a j := by linarith
    have h4 : (a i) * (a j) ≤ (a i + a j) ^ 2 / 4 := by 
      linarith [sq_nonneg (a i - a j)]
    have h5 : (a i) * (a j) / (a i + a j) ≤ (a i + a j) / 4 := by 
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      linarith 
    exact h5

  have h2 : ∑ i : Fin n, ∑ j : Fin n, (a i) * (a j) / (a i + a j) ≤ ∑ i : Fin n, ∑ j : Fin n, (a i + a j) / 4 := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact h1 i j

  have h3 : ∑ i : Fin n, ∑ j : Fin n, (a i + a j) / 4 = (n : ℝ) / 2 := by 
    have h4 : ∑ i : Fin n, ∑ j : Fin n, (a i + a j) / 4 = (∑ i : Fin n, ∑ j : Fin n, (a i + a j)) / 4 := by
      simp [Finset.sum_div]
    rw [h4]
    have h5 : ∑ i : Fin n, ∑ j : Fin n, (a i + a j) = 2 * (n : ℝ) := by
      calc
        ∑ i : Fin n, ∑ j : Fin n, (a i + a j) = ∑ i : Fin n, (∑ j : Fin n, (a i + a j)) := by rw [Finset.sum_comm]
        _ = ∑ i : Fin n, ((n : ℝ) * (a i) + 1) := by
          apply Finset.sum_congr
          . rfl
          intro i hi
          calc
            ∑ j : Fin n, (a i + a j) = ∑ j : Fin n, (a i) + ∑ j : Fin n, (a j) := by 
              rw [Finset.sum_add_distrib]
            _ = (n : ℝ) * (a i) + 1 := by 
              simp [Finset.sum_const, mul_comm, ha]
        _ = (∑ i : Fin n, ((n : ℝ) * (a i))) + (∑ i : Fin n, (1 : ℝ)) := by 
          rw [Finset.sum_add_distrib]
        _ = (n : ℝ) * (∑ i : Fin n, (a i)) + (n : ℝ) := by 
          simp [Finset.sum_const, Finset.mul_sum]
        _ = (n : ℝ) * 1 + (n : ℝ) := by 
          rw [ha]
        _ = 2 * (n : ℝ) := by 
          ring

    rw [h5]
    ring

  linarith [h2, h3]