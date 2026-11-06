import Mathlib

theorem algebra_199235 {n : ℕ} (hn : Odd n) (hn1 : n > 1)
    (M : Fin n → ℝ) (hM : ∀ i, M i = ∑ j ∈ Finset.univ \ {i}, M j) :
    ∏ i, M i = 0 := by

  have h2 : n ≥ 3 := by
    rcases hn with ⟨k, hk⟩
    omega

  have h5 : ∀ i : Fin n, 2 * M i = ∑ j : Fin n, M j := by
    intro i
    have eq1 : M i = ∑ j ∈ Finset.univ \ {i}, M j := hM i
    have eq2 : (∑ j ∈ Finset.univ \ {i}, M j) = (∑ j : Fin n, M j) - M i := by
      rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
      all_goals
        simp
    rw [eq2] at eq1
    linarith

  have h6 : 2 * (∑ i : Fin n, M i) = (↑n : ℝ) * (∑ i : Fin n, M i) := by
    have eq1 : ∀ i : Fin n, 2 * M i = ∑ j : Fin n, M j := h5
    have eq2 : ∑ i : Fin n, (2 * M i) = ∑ i : Fin n, (∑ j : Fin n, M j) := by
      congr
      funext i
      exact eq1 i
    have eq3 : ∑ i : Fin n, (2 * M i) = 2 * (∑ i : Fin n, M i) := by
      rw [Finset.mul_sum]
    have eq4 : ∑ i : Fin n, (∑ j : Fin n, M j) = (↑n : ℝ) * (∑ j : Fin n, M j) := by
      simp [Finset.sum_const, mul_comm]
    rw [eq3, eq4] at eq2
    linarith

  have h8 : (∑ i : Fin n, M i) = 0 := by
    have eq1 : (↑n : ℝ) ≥ (3 : ℝ) := by
      exact_mod_cast show (3 : ℕ) ≤ n by omega
    have eq2 : 2 * (∑ i : Fin n, M i) = (↑n : ℝ) * (∑ i : Fin n, M i) := by
      linarith
    have eq3 : (∑ i : Fin n, M i) * ((↑n : ℝ) - 2) = 0 := by
      linarith
    cases' (mul_eq_zero.mp eq3) with h9 h10
    · -- case (∑ i : Fin n, M i) = 0
      linarith
    · -- case (↑n : ℝ) - 2 = 0
      have eq4 : (↑n : ℝ) = 2 := by linarith
      nlinarith

  have h10 : ∀ i : Fin n, M i = 0 := by
    intro i
    have h11 : 2 * M i = (∑ j : Fin n, M j) := by
      linarith [h5 i]
    have h12 : (∑ j : Fin n, M j) = 0 := by
      linarith [h8]
    linarith

  have h91 : ∃ i : Fin n, M i = 0 := by
    use ⟨0, by omega⟩
    apply h10

  obtain ⟨i, hi⟩ := h91
  have h92 : (∏ i : Fin n, M i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    all_goals
      simpa using hi
  exact h92