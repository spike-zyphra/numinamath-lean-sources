import Mathlib

open Real

theorem inequalities_100271 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) :
    (∑ i, x i) * (∑ i, 1 / x i) ≥ n ^ 2 := by

  have h1 : ∀ i, x i > 0 := by
    intro i
    exact hx i

  have h2 : (∑ i : Fin n, (Real.sqrt (x i) * Real.sqrt (1 / x i))) ^ 2 ≤ (∑ i : Fin n, (Real.sqrt (x i) )^2) * (∑ i : Fin n, (Real.sqrt (1 / x i) )^2) := by
    apply Finset.sum_mul_sq_le_sq_mul_sq

  have h3 : ∑ i : Fin n, (Real.sqrt (x i) * Real.sqrt (1 / x i)) = (n : ℝ) := by
    have h4 : ∀ i : Fin n, Real.sqrt (x i) * Real.sqrt (1 / x i) = 1 := by
      intro i
      have hx_i_pos : x i > 0 := h1 i
      have h5 : (x i) * (1 / x i) = 1 := by
        field_simp
      have h6 : Real.sqrt (x i) * Real.sqrt (1 / x i) = Real.sqrt ((x i) * (1 / x i)) := by
        rw [← Real.sqrt_mul (by linarith)]
      rw [h6]
      rw [h5]
      all_goals norm_num [Real.sqrt_one]

    calc
      ∑ i : Fin n, (Real.sqrt (x i) * Real.sqrt (1 / x i))
          = ∑ i : Fin n, (1 : ℝ) := by
            apply Finset.sum_congr
            · rfl
            · intro i hi
              exact h4 i
      _ = (n : ℝ) := by simp

  have h4 : (∑ i : Fin n, (Real.sqrt (x i) )^2) = (∑ i : Fin n, x i) := by
    apply Finset.sum_congr
    · rfl
    · intro i hi
      have hx_i_pos : x i > 0 := h1 i
      have h7 : (Real.sqrt (x i) )^2 = x i := Real.sq_sqrt (by linarith)
      linarith

  have h5 : (∑ i : Fin n, (Real.sqrt (1 / x i) )^2) = (∑ i : Fin n, 1 / x i) := by
    apply Finset.sum_congr
    · rfl
    · intro i hi
      have hx_i_pos : x i > 0 := h1 i
      have h8 : (1 / x i) > 0 := by
        positivity
      have h9 : (Real.sqrt (1 / x i) )^2 = 1 / x i := Real.sq_sqrt (by linarith)
      linarith

  have h6 : n ^ 2 ≤ (∑ i : Fin n, x i) * (∑ i : Fin n, 1 / x i) := by
    rw [h3] at h2
    rw [h4, h5] at h2
    nlinarith

  exact h6