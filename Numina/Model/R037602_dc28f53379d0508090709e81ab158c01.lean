import Mathlib

open Real
open scoped BigOperators

theorem inequalities_159483 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
  (hx : ∀ i, 0 < x i) :
  (∑ i, x i) / n ≥ n / (∑ i, 1 / x i) := by 
  have h1 : ∀ i, x i > 0 := by 
    intro i 
    exact hx i 
  have h2 : (∑ i, x i) / n ≥ n / (∑ i, 1 / x i) := by 
    have h3 : (∑ i : Fin n, x i) * (∑ i : Fin n, 1 / x i) ≥ (n : ℝ) ^ 2 := by 
      have h5 : (∑ i : Fin n, (Real.sqrt (x i) * Real.sqrt (1 / x i))) = (n : ℝ) := by 
        have h11 : ∀ i : Fin n, Real.sqrt (x i) * Real.sqrt (1 / x i) = (1 : ℝ) := by 
          intro i 
          have hx9 : x i > 0 := h1 i 
          have h9 : (x i) * (1 / x i) = 1 := by 
            field_simp 
          have h10 : Real.sqrt (x i) * Real.sqrt (1 / x i) = Real.sqrt ((x i) * (1 / x i)) := by 
            rw [← Real.sqrt_mul (by linarith)]
          rw [h10]
          rw [h9]
          all_goals 
            norm_num 
        have h12 : (∑ i : Fin n, (Real.sqrt (x i) * Real.sqrt (1 / x i))) = 
            (∑ i : Fin n, (1 : ℝ)) := by 
          congr 
          funext i 
          exact h11 i 
        rw [h12]
        simp [Finset.sum_const, Finset.card_univ]
        <;> ring 
      have h6 : (∑ i : Fin n, (Real.sqrt (x i) * Real.sqrt (1 / x i))) ^ 2 ≤ 
        (∑ i : Fin n, (Real.sqrt (x i) ) ^ 2) * (∑ i : Fin n, (Real.sqrt (1 / x i) ) ^ 2) := by 
        apply Finset.sum_mul_sq_le_sq_mul_sq 
      have h7 : (∑ i : Fin n, (Real.sqrt (x i) ) ^ 2) = (∑ i : Fin n, x i) := by 
        congr 1 
        funext i 
        have hx9 : x i > 0 := h1 i 
        have h9 : (Real.sqrt (x i) ) ^ 2 = x i := by 
          rw [Real.sq_sqrt] 
          linarith 
        simpa using h9 
      have h9 : (∑ i : Fin n, (Real.sqrt (1 / x i) ) ^ 2) = (∑ i : Fin n, 1 / x i) := by 
        congr 1 
        funext i 
        have hx10 : x i > 0 := h1 i
        have h11 : (1 / x i) > 0 := by 
          positivity 
        have h12 : (Real.sqrt (1 / x i) ) ^ 2 = (1 / x i) := by
          rw [Real.sq_sqrt]
          have hx11 : (1 / x i) ≥ 0 := by linarith 
          linarith 
        simpa using h12 
      rw [h7] at h6 
      rw [h9] at h6 
      rw [h5] at h6 
      linarith 
    have h41 : (∑ i : Fin n, x i) / n ≥ n / (∑ i, 1 / x i) := by 
      have h8 : (∑ i : Fin n, 1 / x i) > 0 := by 
        have h7 : ∀ i : Fin n, 1 / x i > 0 := by 
          intro i 
          have h11 : x i > 0 := h1 i 
          positivity 
        have h9 : ∑ i : Fin n, 1 / x i > 0 := by 
          have h10 : ∀ i : Fin n, 1 / x i > 0 := h7 
          have h11 : ∑ i : Fin n, 1 / x i > 0 := by 
            apply Finset.sum_pos 
            · -- Show each term is positive 
              intro i hi 
              specialize h10 i 
              linarith 
            · -- Show the set is non-empty 
              use ⟨0, by omega⟩ 
              simp 
          linarith 
        linarith 
      apply (div_le_div_iff (by positivity) (by positivity)).mpr 
      nlinarith [sq_nonneg ((∑ i : Fin n, x i) - (∑ i : Fin n, 1 / x i)), 
        h3 
      ]
    linarith 
  linarith