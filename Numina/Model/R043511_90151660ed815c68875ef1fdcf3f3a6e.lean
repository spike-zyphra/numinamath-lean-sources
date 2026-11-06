import Mathlib

open Real

theorem inequalities_149336 (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) :
    (∑ i, x i) / n ≥ n / (∑ i, 1 / x i) := by 
  have h2 : ∑ i : Fin n, x i > 0 := by
    apply Finset.sum_pos
    · -- show x i > 0
      intro i hi
      exact hx i
    · -- show nonempty
      use ⟨0, by omega⟩
      simp

  have h3 : ∑ i : Fin n, (1 / x i) > 0 := by
    apply Finset.sum_pos
    · -- show 1 / x i > 0
      intro i hi
      specialize hx i
      have h4 : 0 < x i := hx
      positivity
    · -- show nonempty
      use ⟨0, by omega⟩
      simp

  have h4 : (∑ i : Fin n, x i) * (∑ i : Fin n, (1 / x i)) ≥ (n : ℝ) ^ 2 := by 
    have h5 : (∑ i : Fin n, (sqrt (x i) * sqrt (1 / x i))) = n := by
      have h1 : ∀ i, sqrt (x i) * sqrt (1 / x i) = 1 := by
        intro i
        have h6 : x i > 0 := hx i
        have h7 : sqrt (x i) > 0 := by
          apply Real.sqrt_pos.mpr
          linarith
        have h8 : sqrt (1 / x i) > 0 := by
          apply Real.sqrt_pos.mpr
          positivity
        have h9 : sqrt (x i) * sqrt (1 / x i) = 1 := by
          have h10 : sqrt (x i) * sqrt (1 / x i) = sqrt ((x i) * (1 / x i)) := by 
            rw [← Real.sqrt_mul (by linarith)]
          have h11 : (x i) * (1 / x i) = 1 := by 
            field_simp
          have h12 : sqrt ((x i) * (1 / x i)) = 1 := by 
            rw [h11]
            exact Real.sqrt_one
          linarith [h10, h12]
        exact h9
      have h10 : ∑ i : Fin n, (sqrt (x i) * sqrt (1 / x i)) = ∑ i : Fin n, 1 := by 
        apply Finset.sum_congr 
        · rfl
        · intro i hi
          exact h1 i
      rw [h10]
      simp [Finset.sum_const, Finset.card_univ, hn]

    have h11 : (∑ i : Fin n, (sqrt (x i) ^ 2)) = ∑ i : Fin n, x i := by
      apply Finset.sum_congr
      · rfl
      · intro i hi
        have h9 : x i > 0 := hx i
        have : (sqrt (x i) : ℝ) ^ 2 = x i := by
          rw [Real.sq_sqrt]
          linarith
        linarith

    have h12 : (∑ i : Fin n, (sqrt (1 / x i) ^ 2)) = ∑ i : Fin n, (1 / x i) := by
      apply Finset.sum_congr
      · rfl
      · intro i hi
        have h9 : x i > 0 := hx i
        have h10 : (1 / x i) > 0 := by positivity
        have : (sqrt (1 / x i) : ℝ) ^ 2 = 1 / x i := by
          rw [Real.sq_sqrt]
          positivity
        linarith

    have h13 : (∑ i : Fin n, (sqrt (x i) ^ 2)) * (∑ i : Fin n, (sqrt (1 / x i) ^ 2)) ≥ (∑ i : Fin n, (sqrt (x i) * sqrt (1 / x i))) ^ 2 := by
      apply Finset.sum_mul_sq_le_sq_mul_sq

    rw [h11, h12, h5] at h13
    nlinarith

  have h6 : (∑ i : Fin n, x i) / n ≥ n / (∑ i : Fin n, 1 / x i) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  exact h6