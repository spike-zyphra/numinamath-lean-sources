import Mathlib

open Real

theorem other_267975 (n : ℕ) (hn : n > 0) (a : Fin n → ℝ)
    (ha : ∀ i, |a i - (∑ j, a j) / n| ≤ 39) :
    √((∑ i, (a i - (∑ j, a j) / n)^2) / n) ≤ 39 := by

  have h1 : ∀ i : Fin n, (a i - (∑ j, a j) / n) ^ 2 ≤ 1521 := by
    intro i
    have h2 : |a i - (∑ j, a j) / n| ≤ 39 := ha i
    have h3 : -39 ≤ a i - (∑ j, a j) / n := by
      linarith [abs_le.mp h2]
    have h4 : a i - (∑ j, a j) / n ≤ 39 := by
      linarith [abs_le.mp h2]
    nlinarith [sq_nonneg (a i - (∑ j, a j) / n + 39), sq_nonneg (a i - (∑ j, a j) / n - 39)]

  have h2 : (∑ i : Fin n, (a i - (∑ j, a j) / n) ^ 2) ≤ n * 1521 := by
    calc
      (∑ i : Fin n, (a i - (∑ j, a j) / n) ^ 2)
        = ∑ i : Fin n, ((a i - (∑ j, a j) / n) ^ 2) := by rfl
      _ ≤ ∑ i : Fin n, (1521 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        specialize h1 i
        linarith
      _ = (n * (1521 : ℝ)) := by
        simp [Finset.sum_const, Finset.card_univ]
      _ = (n * 1521 : ℝ) := by ring

  have h3 : (∑ i, (a i - (∑ j, a j) / n)^2) / n ≤ (1521 : ℝ) := by
    have h4 : (n : ℝ) > 0 := by exact_mod_cast show (0 : ℕ) < n by linarith
    have h5 : (∑ i, (a i - (∑ j, a j) / n)^2) / n ≤ (1521 : ℝ) := by
      have h6 : (∑ i : Fin n, (a i - (∑ j, a j) / n) ^ 2) ≤ (n * 1521 : ℝ) := h2
      have h7 : (∑ i, (a i - (∑ j, a j) / n)^2) / n ≤ (1521 : ℝ) := by
        have h8 : (∑ i, (a i - (∑ j, a j) / n)^2 : ℝ) = (∑ i, (a i - (∑ j, a j) / n)^2 : ℝ) := by rfl
        rw [h8]
        have h9 : (∑ i : Fin n, (a i - (∑ j, a j) / n) ^ 2 : ℝ) / (n : ℝ) ≤ (1521 : ℝ) := by
          have h10 : (∑ i : Fin n, (a i - (∑ j, a j) / n) ^ 2) ≤ (n * 1521 : ℝ) := h2
          have h11 : (∑ i : Fin n, (a i - (∑ j, a j) / n) ^ 2 : ℝ) / (n : ℝ) ≤ (1521 : ℝ) := by
            have h12 : (n : ℝ) > 0 := by exact_mod_cast show (0 : ℕ) < n by linarith
            apply (div_le_iff₀ (by positivity)).mpr
            nlinarith
          linarith
        have h12 : (∑ i : Fin n, (a i - (∑ j, a j) / n) ^ 2 : ℝ) / (n : ℝ) = (∑ i, (a i - (∑ j, a j) / n)^2) / n := by
          rfl
        linarith
      linarith
    linarith

  have h4 : √((∑ i, (a i - (∑ j, a j) / n)^2) / n) ≤ (39 : ℝ) := by
    have h5 : (∑ i, (a i - (∑ j, a j) / n)^2) / n ≤ (1521 : ℝ) := h3
    have h6 : √((∑ i, (a i - (∑ j, a j) / n)^2) / n) ≤ √(1521 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h7 : √((1521 : ℝ)) = (39 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    linarith [h7, h6]

  exact h4