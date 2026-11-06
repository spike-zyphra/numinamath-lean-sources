import Mathlib

open BigOperators Real Set

lemma lemma_1 (x₁ x₂ : ℝ) (a : ℝ) (h₁ : 0 ≤ a) (h₂ : a ≤ 2) (h₃ : Real.sin x₁ ^ 2 + Real.sin x₂ ^ 2 = a) :
  |Real.sin (2 * x₁) + Real.sin (2 * x₂)| ≤ 2 * Real.sqrt ((a) * (2 - a)) := by
  have eq1 : Real.sin (2 * x₁) = 2 * Real.sin x₁ * Real.cos x₁ := by
    rw [Real.sin_two_mul]
  have eq2 : Real.sin (2 * x₂) = 2 * Real.sin x₂ * Real.cos x₂ := by
    rw [Real.sin_two_mul]
  have eq3 : Real.sin (2 * x₁) + Real.sin (2 * x₂) = 2 * (Real.sin x₁ * Real.cos x₁ + Real.sin x₂ * Real.cos x₂) := by
    rw [eq1, eq2]
    all_goals ring
  have h4 : Real.sin x₁ ^ 2 + Real.sin x₂ ^ 2 = a := h₃
  have h5 : Real.cos x₁ ^ 2 + Real.cos x₂ ^ 2 = 2 - a := by
    have h6 : Real.cos x₁ ^ 2 + Real.cos x₂ ^ 2 = 2 - (Real.sin x₁ ^ 2 + Real.sin x₂ ^ 2) := by
      have h7 : Real.sin x₁ ^ 2 + Real.cos x₁ ^ 2 = 1 := Real.sin_sq_add_cos_sq x₁
      have h8 : Real.sin x₂ ^ 2 + Real.cos x₂ ^ 2 = 1 := Real.sin_sq_add_cos_sq x₂
      nlinarith
    rw [h6, h₃]
  have h6 : (Real.sin x₁ * Real.cos x₁ + Real.sin x₂ * Real.cos x₂) ^ 2 ≤ (a) * (2 - a) := by
    nlinarith [sq_nonneg (Real.sin x₁ * Real.cos x₂ - Real.sin x₂ * Real.cos x₁), sq_nonneg (Real.sin x₁ ^ 2 + Real.sin x₂ ^ 2 - (Real.cos x₁ ^ 2 + Real.cos x₂ ^ 2)), sq_nonneg (Real.sin x₁ - Real.sin x₂), sq_nonneg (Real.cos x₁ - Real.cos x₂), Real.sin_sq_add_cos_sq x₁, Real.sin_sq_add_cos_sq x₂, mul_nonneg (show 0 ≤ (a) by linarith) (show 0 ≤ (2 - a) by linarith)]
  have h7 : |Real.sin (2 * x₁) + Real.sin (2 * x₂)| = 2 * |Real.sin x₁ * Real.cos x₁ + Real.sin x₂ * Real.cos x₂| := by
    rw [eq3]
    have h9 : |(2 : ℝ) * (Real.sin x₁ * Real.cos x₁ + Real.sin x₂ * Real.cos x₂)| = (2 : ℝ) * |Real.sin x₁ * Real.cos x₁ + Real.sin x₂ * Real.cos x₂| := by
      simp [abs_mul]
    linarith [h9]
  have h8 : |Real.sin x₁ * Real.cos x₁ + Real.sin x₂ * Real.cos x₂| ≤ Real.sqrt ((a) * (2 - a)) := by
    have h9 : (Real.sin x₁ * Real.cos x₁ + Real.sin x₂ * Real.cos x₂) ^ 2 ≤ (a) * (2 - a) := h6
    have h10 : |Real.sin x₁ * Real.cos x₁ + Real.sin x₂ * Real.cos x₂| = Real.sqrt ((Real.sin x₁ * Real.cos x₁ + Real.sin x₂ * Real.cos x₂) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    have h11 : Real.sqrt ((Real.sin x₁ * Real.cos x₁ + Real.sin x₂ * Real.cos x₂) ^ 2) ≤ Real.sqrt ((a) * (2 - a)) := by
      apply Real.sqrt_le_sqrt
      linarith
    linarith [h10, h11]
  have h9 : 2 * |Real.sin x₁ * Real.cos x₁ + Real.sin x₂ * Real.cos x₂| ≤ 2 * Real.sqrt ((a) * (2 - a)) := by
    linarith [h8]
  linarith [h7, h9]

theorem algebra_603771 {n : ℕ} (a : ℝ) (ha : 0 ≤ a ∧ a ≤ n)
  (x : Fin n → ℝ) (h : ∑ i : Fin n, (sin (x i))^2 = a) :
  ∑ i : Fin n, sin (2 * x i) ≤ 2 * sqrt (a * (n - a)) := by
  have h_n1 : 0 ≤ a := by linarith [ha.1]
  have h_n2 : a ≤ n := by linarith [ha.2]
  have h_n3 : ∑ i : Fin n, Real.sin (x i) ^ 2 = a := by
    simpa using h
  have h_n4 : ∑ i : Fin n, Real.cos (x i) ^ 2 = (n : ℝ) - a := by
    have h_n9 : ∑ i : Fin n, Real.cos (x i) ^ 2 = ∑ i : Fin n, (1 - Real.sin (x i) ^ 2) := by
      apply Finset.sum_congr
      . rfl
      intro i hi
      have h10 : Real.cos (x i) ^ 2 = 1 - Real.sin (x i) ^ 2 := by
        have h10 : Real.sin (x i) ^ 2 + Real.cos (x i) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x i)
        linarith
      linarith
    rw [h_n9]
    calc
      ∑ i : Fin n, (1 - Real.sin (x i) ^ 2) = ∑ i : Fin n, (1 : ℝ) - ∑ i : Fin n, Real.sin (x i) ^ 2 := by
        rw [Finset.sum_sub_distrib]
      _ = (n : ℝ) - ∑ i : Fin n, Real.sin (x i) ^ 2 := by
        simp
      _ = (n : ℝ) - a := by
        rw [h_n3]
  have h_n5 : ∑ i : Fin n, Real.sin (2 * (x i)) = 2 * (∑ i : Fin n, (Real.sin (x i) * Real.cos (x i))) := by
    have h10 : ∑ i : Fin n, Real.sin (2 * (x i)) = ∑ i : Fin n, (2 * (Real.sin (x i) * Real.cos (x i)) ) := by
      apply Finset.sum_congr
      . rfl
      intro i hi
      have h11 : Real.sin (2 * (x i)) = 2 * Real.sin (x i) * Real.cos (x i) := by
        rw [Real.sin_two_mul]
      linarith [h11]
    rw [h10]
    simp [Finset.mul_sum]
  rw [h_n5]
  have h_n6 : (∑ i : Fin n, (Real.sin (x i) * Real.cos (x i))) ^ 2 ≤ a * ((n : ℝ) - a) := by
    have h_n7 : (∑ i : Fin n, (Real.sin (x i) * Real.cos (x i))) ^ 2 ≤ (∑ i : Fin n, (Real.sin (x i) ^ 2)) * (∑ i : Fin n, (Real.cos (x i) ^ 2)) := by
      apply Finset.sum_mul_sq_le_sq_mul_sq
    rw [h_n3, h_n4] at h_n7
    nlinarith [mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ (n : ℝ) - a by nlinarith)]
  have h20 : ∑ i : Fin n, (Real.sin (x i) * Real.cos (x i)) ≤ Real.sqrt (a * ((n : ℝ) - a)) := by
    have h21 : (∑ i : Fin n, (Real.sin (x i) * Real.cos (x i)) ) ^ 2 ≤ a * ((n : ℝ) - a) := h_n6
    have h22 : 0 ≤ Real.sqrt (a * ((n : ℝ) - a)) := Real.sqrt_nonneg (a * ((n : ℝ) - a))
    have h23 : Real.sqrt ((∑ i : Fin n, (Real.sin (x i) * Real.cos (x i)) ) ^ 2) ≤ Real.sqrt (a * ((n : ℝ) - a)) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h100 : Real.sqrt ((∑ i : Fin n, (Real.sin (x i) * Real.cos (x i)) ) ^ 2) = |∑ i : Fin n, (Real.sin (x i) * Real.cos (x i))| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h100] at h23
    cases' abs_cases (∑ i : Fin n, (Real.sin (x i) * Real.cos (x i)) ) with h99 h99
    · -- case where the sum is non-negative
      nlinarith [h99, h23]
    · -- case where the sum is negative
      nlinarith [h99, h23]
  nlinarith [Real.sqrt_nonneg (a * ((n : ℝ) - a)), Real.sq_sqrt (show 0 ≤ a * ((n : ℝ) - a) by nlinarith)]