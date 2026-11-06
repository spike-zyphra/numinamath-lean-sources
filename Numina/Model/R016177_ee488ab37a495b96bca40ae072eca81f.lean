import Mathlib

theorem algebra_316349 (x : Fin 10 → ℝ)
    (h₁ : ∑ i, abs (x i - 1) ≤ 4)
    (h₂ : ∑ i, abs (x i - 2) ≤ 6) :
    (∑ i, x i) / 10 = 1.4 := by
  have h3 : ∑ i : Fin 10, (x i - 1) ≤ 4 := by
    have h4 : ∑ i : Fin 10, (x i - 1) ≤ ∑ i : Fin 10, abs (x i - 1) := by
      have h5 : ∀ i : Fin 10, (x i - 1) ≤ abs (x i - 1) := by
        intro i
        cases' abs_cases (x i - 1) with h h
        · linarith
        · linarith
      calc
        ∑ i : Fin 10, (x i - 1) = ∑ i : Fin 10, ((x i - 1) : ℝ) := by rfl
        _ ≤ ∑ i : Fin 10, abs (x i - 1) := by
          apply Finset.sum_le_sum
          intro i _
          apply h5 i
    have h6 : ∑ i : Fin 10, abs (x i - 1) ≤ (4 : ℝ) := by linarith [h₁]
    linarith
  have h7 : ∑ i, x i ≤ 14 := by
    have h8 : ∑ i : Fin 10, (x i - 1) = (∑ i : Fin 10, x i) - 10 := by
      simp [Finset.sum_sub_distrib]
    rw [h8] at h3
    linarith
  have h9 : ∑ i : Fin 10, (2 - x i) ≤ 6 := by
    have h10 : ∑ i : Fin 10, (2 - x i) ≤ ∑ i : Fin 10, abs (x i - 2) := by
      have h11 : ∀ i : Fin 10, (2 - x i) ≤ abs (x i - 2) := by
        intro i
        cases' abs_cases (x i - 2) with h h
        · linarith
        · linarith
      calc
        ∑ i : Fin 10, (2 - x i) = ∑ i : Fin 10, ((2 - x i) : ℝ) := by rfl
        _ ≤ ∑ i : Fin 10, abs (x i - 2) := by
          apply Finset.sum_le_sum
          intro i _
          have h := h11 i
          linarith
    have h12 : ∑ i : Fin 10, abs (x i - 2) ≤ (6 : ℝ) := by linarith [h₂]
    linarith
  have h8 : ∑ i : Fin 10, x i ≥ 14 := by
    have h13 : ∑ i : Fin 10, (2 - x i) = 20 - (∑ i : Fin 10, x i) := by
      simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
      all_goals ring
    linarith [h13, h9]
  have h12 : ∑ i, x i = 14 := by linarith
  calc
    (∑ i, x i) / 10 = (14 : ℝ) / 10 := by rw [h12]
    _ = 1.4 := by norm_num