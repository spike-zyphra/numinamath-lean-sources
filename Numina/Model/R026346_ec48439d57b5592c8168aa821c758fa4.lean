import Mathlib

open Real

theorem inequalities_277227 (n : ℕ) (x y : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    ∑ i, sqrt (x i * y i) ≤
    sqrt (∑ i, x i) * sqrt (∑ i, y i) := by

  have h1 : ∀ i : Fin n, sqrt (x i * y i) = sqrt (x i) * sqrt (y i) := by
    intro i
    rw [Real.sqrt_mul (by linarith [hx i, hy i])]

  have h2 : ∑ i : Fin n, sqrt (x i * y i) = ∑ i : Fin n, (sqrt (x i) * sqrt (y i)) := by
    congr
    funext i
    apply h1

  rw [h2]

  have h3 : (∑ i : Fin n, (sqrt (x i) * sqrt (y i))) ^ 2 ≤ (∑ i : Fin n, (sqrt (x i) ^ 2)) * (∑ i : Fin n, (sqrt (y i) ^ 2)) := by
    apply Finset.sum_mul_sq_le_sq_mul_sq

  have h4 : ∑ i : Fin n, (sqrt (x i) ^ 2) = ∑ i : Fin n, (x i) := by
    apply Finset.sum_congr
    · rfl
    · intro i hi
      have h1i : 0 < x i := hx i
      have h5 : sqrt (x i) ^ 2 = x i := Real.sq_sqrt (le_of_lt h1i)
      linarith [h5]

  have h5 : ∑ i : Fin n, (sqrt (y i) ^ 2) = ∑ i : Fin n, (y i) := by
    apply Finset.sum_congr
    · rfl
    · intro i hi
      have h1i : 0 < y i := hy i
      have h6 : sqrt (y i) ^ 2 = y i := Real.sq_sqrt (le_of_lt h1i)
      linarith [h6]

  have h6 : (∑ i : Fin n, (sqrt (x i) * sqrt (y i))) ^ 2 ≤ (∑ i : Fin n, (x i)) * (∑ i : Fin n, (y i)) := by
    rw [h4, h5] at h3
    linarith

  have h8 : sqrt ((∑ i : Fin n, (sqrt (x i) * sqrt (y i))) ^ 2) = ∑ i : Fin n, (sqrt (x i) * sqrt (y i)) := by
    have h11 : 0 ≤ ∑ i : Fin n, (sqrt (x i) * sqrt (y i)) := by
      apply Finset.sum_nonneg
      intro i hi
      have h11 : sqrt (x i) ≥ 0 := Real.sqrt_nonneg (x i)
      have h12 : sqrt (y i) ≥ 0 := Real.sqrt_nonneg (y i)
      have h13 : sqrt (x i) * sqrt (y i) ≥ 0 := mul_nonneg h11 h12
      exact h13
    have h12 : ( (∑ i : Fin n, (sqrt (x i) * sqrt (y i))) ^ 2 ) = (∑ i : Fin n, (sqrt (x i) * sqrt (y i))) ^ 2 := by rfl
    rw [h12]
    rw [Real.sqrt_sq (show 0 ≤ ∑ i : Fin n, (sqrt (x i) * sqrt (y i)) by linarith)]

  have h9 : sqrt ((∑ i : Fin n, (x i)) * (∑ i : Fin n, (y i)) ) = sqrt (∑ i, x i) * sqrt (∑ i, y i) := by
    rw [Real.sqrt_mul (by
      have h11 : ∑ i : Fin n, (x i) ≥ 0 := by
        apply Finset.sum_nonneg
        intro i hi
        linarith [hx i]
      linarith [h11]
    )]

  have h7 : sqrt ((∑ i : Fin n, (sqrt (x i) * sqrt (y i))) ^ 2) ≤ sqrt ((∑ i : Fin n, (x i)) * (∑ i : Fin n, (y i)) ) := by
    apply Real.sqrt_le_sqrt
    linarith [h6]

  linarith [h8, h7, h9]