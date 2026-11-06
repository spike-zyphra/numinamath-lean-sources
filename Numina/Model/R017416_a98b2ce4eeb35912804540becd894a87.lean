import Mathlib

open Finset Real

theorem inequalities_599238 (n : ℕ) (a : Fin n → ℝ) (x : Fin n → ℝ)
    (h₀ : ∀ i, 0 < a i) (h₁ : ∑ i, a i = 1) :
    ∑ i, a i * (x i)^2 ≥ (∑ i, a i * x i)^2 := by

  have h4 : (∑ i : Fin n, a i * x i) ^ 2 = (∑ i : Fin n, (√(a i) * x i) * (√(a i)) ) ^ 2 := by
    have h3 : (∑ i : Fin n, (√(a i) * x i) * (√(a i)) ) = (∑ i : Fin n, a i * x i) := by
      apply Finset.sum_congr
      · rfl
      · intro i _
        have h3 : 0 < a i := h₀ i
        have h4 : 0 ≤ a i := by linarith
        have h2 : (√(a i) * x i) * (√(a i)) = a i * x i := by
          calc
            (√(a i) * x i) * (√(a i)) = √(a i) * (√(a i) * x i) := by ring
            _ = (√(a i) * √(a i)) * x i := by ring
            _ = (a i) * x i := by
              have h5 : (√(a i)) ^ 2 = a i := Real.sq_sqrt (show (0 : ℝ) ≤ a i by linarith)
              have h6 : √(a i) * √(a i) = a i := by nlinarith
              rw [h6]
            _ = a i * x i := by ring
        linarith
    rw [h3]

  have h6 : (∑ i : Fin n, (√(a i) * x i) * (√(a i)) ) ^ 2 ≤ (∑ i : Fin n, ((√(a i) * x i) ^ 2)) * (∑ i : Fin n, ((√(a i)) ^ 2)) := by
    apply Finset.sum_mul_sq_le_sq_mul_sq

  have h7 : ∑ i : Fin n, ((√(a i) * x i) ^ 2) = ∑ i : Fin n, a i * (x i) ^ 2 := by
    apply Finset.sum_congr
    · rfl
    · intro i _
      have h3 : 0 < a i := h₀ i
      have h4 : 0 ≤ a i := by linarith
      calc
        (√(a i) * x i) ^ 2 = (√(a i) ^ 2) * (x i ^ 2) := by ring
        _ = (a i) * (x i ^ 2) := by
          have h5 : (√(a i)) ^ 2 = a i := Real.sq_sqrt (show (0 : ℝ) ≤ a i by linarith)
          rw [h5]
        _ = a i * (x i) ^ 2 := by ring

  have h8 : ∑ i : Fin n, ((√(a i)) ^ 2) = ∑ i : Fin n, a i := by
    apply Finset.sum_congr
    · rfl
    · intro i _
      have h3 : 0 < a i := h₀ i
      have h4 : 0 ≤ a i := by linarith
      have h5 : (√(a i)) ^ 2 = a i := Real.sq_sqrt (show (0 : ℝ) ≤ a i by linarith)
      linarith

  have h9 : (∑ i : Fin n, a i * x i) ^ 2 ≤ (∑ i : Fin n, a i * (x i)^2) := by
    calc
      (∑ i : Fin n, a i * x i) ^ 2 = (∑ i : Fin n, (√(a i) * x i) * (√(a i)) ) ^ 2 := by
        linarith [h4]
      _ ≤ (∑ i : Fin n, ((√(a i) * x i) ^ 2)) * (∑ i : Fin n, ((√(a i)) ^ 2)) := h6
      _ = (∑ i : Fin n, a i * (x i)^2) := by
        rw [h7, h8]
        rw [h₁]
        all_goals norm_num
  linarith