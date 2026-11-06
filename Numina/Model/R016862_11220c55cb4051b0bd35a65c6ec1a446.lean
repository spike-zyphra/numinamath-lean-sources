import Mathlib

open Finset Real

theorem inequalities_38173 {n : ℕ} (hn : 0 < n) (a : ℕ → ℤ)
    (ha : ∀ i ∈ range n, 0 < a i) :
    (∏ i ∈ range n, (a i ^ 2 + 3 * a i + 1)) / (∏ i ∈ range n, a i) ≥ 2 ^ (2 * n) := by

  have h1 : (∏ i ∈ range n, (a i ^ 2 + 3 * a i + 1)) ≥ (4 : ℤ) ^ n * (∏ i ∈ range n, a i) := by
    have h2 : ∀ i ∈ range n, (a i)^2 + 3 * (a i) + 1 ≥ 4 * (a i) := by
      intro i hi
      have ha_i : 0 < a i := ha i hi
      have h3 : (a i)^2 - (a i) + 1 ≥ 0 := by
        nlinarith [sq_nonneg ((a i) : ℤ), sq_nonneg ((a i) - 1 : ℤ), sq_pos_of_pos (show 0 < (a i) by exact ha_i)]
      nlinarith

    have h3 : (∏ i ∈ range n, ((a i)^2 + 3 * (a i) + 1)) ≥ (∏ i ∈ range n, (4 * (a i)) : ℤ) := by
      apply Finset.prod_le_prod
      · -- Show that $0 \leq 4 \cdot a_i$ for all $i \in range \ n$.
        intro i hi
        have ha_i : 0 < a i := ha i hi
        nlinarith
      · -- Show that $4 \cdot a_i \leq a_i^2 + 3 \cdot a_i + 1$ for all $i \in range \ n$.
        intro i hi
        specialize h2 i hi
        linarith

    have h4 : (∏ i ∈ range n, (4 * (a i)) : ℤ) = (4 ^ n : ℤ) * (∏ i ∈ range n, (a i)) := by
      calc
        (∏ i ∈ range n, (4 * (a i)) : ℤ)
          = ∏ i ∈ range n, ((4 : ℤ) * (a i : ℤ)) := by
            apply Finset.prod_congr
            · rfl
            · intro i hi
              ring
        _ = (∏ i ∈ range n, (4 : ℤ)) * (∏ i ∈ range n, (a i : ℤ)) := by
          rw [prod_mul_distrib]
        _ = (4 ^ n : ℤ) * (∏ i ∈ range n, (a i : ℤ)) := by
          have h6 : (∏ i ∈ range n, (4 : ℤ)) = (4 ^ n : ℤ) := by
            simp [prod_const]
          rw [h6]

    linarith [h3, h4]

  have h2 : (∏ i ∈ range n, a i) > 0 := by
    apply Finset.prod_pos
    intro i hi
    have ha_i : 0 < a i := ha i hi
    linarith

  have h3 : (∏ i ∈ range n, (a i ^ 2 + 3 * a i + 1)) / (∏ i ∈ range n, a i) ≥ (4 ^ n : ℤ) := by
    have h5 : (∏ i ∈ range n, (a i ^ 2 + 3 * a i + 1)) ≥ (4 ^ n : ℤ) * (∏ i ∈ range n, a i) := h1
    have h6 : (∏ i ∈ range n, (a i ^ 2 + 3 * a i + 1)) / (∏ i ∈ range n, a i) ≥ (4 ^ n : ℤ) := by
      apply Int.le_ediv_of_mul_le
      all_goals
      linarith
    linarith

  have h5 : (4 ^ n : ℤ) = (2 ^ (2 * n) : ℤ) := by
    have h2 : (4 ^ n : ℤ) = (2 ^ (2 * n) : ℤ) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
      rw [← pow_mul]
    linarith

  linarith [h3, h5]