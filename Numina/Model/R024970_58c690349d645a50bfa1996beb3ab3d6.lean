import Mathlib

open Real

theorem inequalities_51375 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    ∃ x : Fin n → ℝ,
      (∀ i, 0 < x i) ∧
      (∑ i, x i) = 1 ∧
      (∀ y : Fin n → ℝ,
        (∀ i, 0 < y i) ∧
        (∑ i, y i) = 1 →
        ∑ i, a i * x i / (x i + y i) ≥ 1 / 2 * ∑ i, a i) := by

  use fun i => (a i) / (∑ j : Fin n, a j)

  constructor
  · -- Show that all x_i are positive.
    intro i
    have h1 : 0 < ∑ j : Fin n, a j := by
      apply Finset.sum_pos
      · intro i hi
        exact ha i
      · use ⟨0, hn⟩
        simp
    have h2 : 0 < a i := ha i
    positivity

  constructor
  · -- Show that the sum of x_i is 1.
    have h1 : 0 < ∑ j : Fin n, a j := by
      apply Finset.sum_pos
      · intro i hi
        exact ha i
      · use ⟨0, hn⟩
        simp
    calc
      ∑ i : Fin n, ((a i) / (∑ j : Fin n, a j)) 
          = (∑ i : Fin n, a i) / (∑ j : Fin n, a j) := by 
            rw [Finset.sum_div]
      _ = (∑ j : Fin n, a j) / (∑ j : Fin n, a j) := by 
        rfl
      _ = 1 := by 
        field_simp

  · -- Show that the inequality holds.
    intro y h
    rcases h with ⟨hy_pos, hy_sum⟩
    have h1 : 0 < ∑ j : Fin n, a j := by
      apply Finset.sum_pos
      · intro i hi
        exact ha i
      · use ⟨0, hn⟩
        simp

    have h7 : ∑ i : Fin n, (a i * ((a i) / (∑ j : Fin n, a j)) / (( (a i) / (∑ j : Fin n, a j) ) + y i)) ≥ 1 / 2 * ∑ i : Fin n, a i := by
      have h14 : ∑ i : Fin n, (a i * ((a i) / (∑ j : Fin n, a j)) / (( (a i) / (∑ j : Fin n, a j) ) + y i)) = ∑ i : Fin n, (a i ^ 2 / (a i + (∑ j : Fin n, a j) * y i)) := by
        apply Finset.sum_congr
        · rfl
        intro i hi
        have h15 : a i > 0 := ha i
        have h16 : y i > 0 := hy_pos i
        have h17 : ∑ j : Fin n, a j > 0 := by
          apply Finset.sum_pos
          · intro i hi
            exact ha i
          · use ⟨0, hn⟩
            simp

        have h18 : (a i * ((a i) / (∑ j : Fin n, a j)) / (( (a i) / (∑ j : Fin n, a j) ) + y i)) = (a i ^ 2 / (a i + (∑ j : Fin n, a j) * y i)) := by
          field_simp [show (∑ j : Fin n, a j) ≠ 0 by positivity]
          all_goals nlinarith

        exact h18

      rw [h14] at *
      have h5 : ∑ i : Fin n, (a i ^ 2 / (a i + (∑ j : Fin n, a j) * y i)) ≥ (∑ i : Fin n, a i) ^ 2 / (2 * (∑ j : Fin n, a j)) := by
        have h6 : ∑ i : Fin n, (a i ^ 2 / (a i + (∑ j : Fin n, a j) * y i)) ≥ (∑ i : Fin n, a i) ^ 2 / (∑ i : Fin n, (a i + (∑ j : Fin n, a j) * y i)) := by
          apply Finset.sq_sum_div_le_sum_sq_div
          intro i hi
          have h17 : a i + (∑ j : Fin n, a j) * y i > 0 := by
            have h3 : a i > 0 := ha i
            have h4 : y i > 0 := hy_pos i
            positivity
          exact h17

        have h0' : (∑ i : Fin n, (a i + (∑ j : Fin n, a j) * y i)) = 2 * (∑ j : Fin n, a j) := by
          calc
            ∑ i : Fin n, (a i + (∑ j : Fin n, a j) * y i) 
              = ∑ i : Fin n, (a i) + (∑ j : Fin n, a j) * (∑ i : Fin n, y i) := by
                rw [Finset.sum_add_distrib]
                rw [Finset.mul_sum]
            _ = (∑ i : Fin n, a i) + (∑ j : Fin n, a j) * (∑ i : Fin n, y i) := by 
              rfl
            _ = (∑ i : Fin n, a i) + (∑ j : Fin n, a j) * 1 := by 
              rw [show ∑ i : Fin n, y i = 1 by linarith [hy_sum]]
            _ = (∑ i : Fin n, a i) + (∑ j : Fin n, a j) := by 
                ring
            _ = 2 * (∑ j : Fin n, a j) := by 
              ring

        rw [h0'] at h6
        linarith

      have h13 : (∑ i : Fin n, a i) ^ 2 / (2 * (∑ j : Fin n, a j)) ≥ 1 / 2 * ∑ i, a i := by
        have h17 : (∑ i : Fin n, a i) > 0 := by
          apply Finset.sum_pos
          · intro i hi
            exact ha i
          · use ⟨0, hn⟩
            simp
        have h34 : (∑ i, a i) ^ 2 / (2 * (∑ j, a j)) ≥ (∑ i, a i) / 2 := by
          have h17 : (∑ i : Fin n, a i) > 0 := h17
          have h15 : (∑ i, a i) ^ 2 / (2 * (∑ j, a j)) = (∑ i, a i) / 2 := by
            have h9 : (∑ i : Fin n, a i) > 0 := h17
            field_simp [show (∑ j, a j) ≠ 0 by positivity]
            all_goals nlinarith
          nlinarith

        linarith

      nlinarith

    linarith