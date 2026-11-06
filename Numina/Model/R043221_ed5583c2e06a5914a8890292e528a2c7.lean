import Mathlib

theorem other_267983 (n : ℕ) (hn : n > 0) (a : Fin n → ℝ)
    (ha : ∀ i, |a i - (∑ j, a j) / n| ≤ 37) :
    √((∑ i, (a i - (∑ j, a j) / n)^2) / n) ≤ 37 := by
  have h1 : ∀ i : Fin n, (a i - (∑ j : Fin n, a j) / (n : ℝ)) ^ 2 ≤ 37 ^ 2 := by
    intro i
    have h2 : |a i - (∑ j : Fin n, a j) / (n : ℝ)| ≤ 37 := ha i
    have h3 : -37 ≤ a i - (∑ j : Fin n, a j) / (n : ℝ) := by
      linarith [abs_le.mp h2]
    have h4 : a i - (∑ j : Fin n, a j) / (n : ℝ) ≤ 37 := by
      linarith [abs_le.mp h2]
    nlinarith

  have h2 : (∑ i : Fin n, (a i - (∑ j : Fin n, a j) / (n : ℝ)) ^ 2) ≤ (n : ℝ) * (37 ^ 2 : ℝ) := by
    have h3 : ∀ i : Fin n, (a i - (∑ j : Fin n, a j) / (n : ℝ)) ^ 2 ≤ 37 ^ 2 := h1
    have h4 : ∑ i : Fin n, (a i - (∑ j : Fin n, a j) / (n : ℝ)) ^ 2 ≤
        ∑ i : Fin n, (37 ^ 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      specialize h3 i
      simpa using h3
    have h5 : ∑ i : Fin n, (37 ^ 2 : ℝ) = (n : ℝ) * (37 ^ 2 : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ, mul_comm]
      <;> ring
    rw [h5] at h4
    linarith

  have h3 : (∑ i : Fin n, (a i - (∑ j : Fin n, a j) / (n : ℝ)) ^ 2) / (n : ℝ) ≤ (37 ^ 2 : ℝ) := by
    have hn' : (n : ℝ) > 0 := by exact_mod_cast show n > (0 : ℕ) by linarith
    apply (div_le_iff₀ hn').mpr
    linarith [h2]

  have h4 : Real.sqrt ((∑ i : Fin n, (a i - (∑ j : Fin n, a j) / (n : ℝ)) ^ 2) / (n : ℝ)) ≤ Real.sqrt (37 ^ 2 : ℝ) := by
    apply Real.sqrt_le_sqrt
    linarith [h3]

  have h6 : Real.sqrt (37 ^ 2 : ℝ) = (37 : ℝ) := by
    rw [Real.sqrt_sq]
    all_goals norm_num
  rw [h6] at h4
  linarith [h4]