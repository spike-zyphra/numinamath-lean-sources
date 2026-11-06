import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_319172 {f : ℝ → ℝ}
  (hf : ∀ x, f x = (2 ^ x + 1) ^ 2 / (2 ^ x * x) + 1)
  (M N : ℝ)
  (hM : ∃ x ∈ Ico (-2018) 0, f x = M)
  (hN : ∃ x ∈ Ioc 0 2018, f x = N)
  (hMub : ∀ x ∈ Ico (-2018) 0, f x ≤ M)
  (hNlb : ∀ x ∈ Ioc 0 2018, f x ≥ N) :
  M + N = 2 := by

  rcases hM with ⟨x₁, hx₁, hx₁'⟩
  rcases hN with ⟨x₂, hx₂, hx₂'⟩

  have h1 : -x₂ ∈ Ico (-2018) 0 := by
    rcases mem_Ioc.mp hx₂ with ⟨hx₂1, hx₂2⟩
    constructor
    · linarith
    · linarith

  have h2 : f (-x₂) ≤ M := by
    apply hMub
    exact h1

  have h3 : f x₂ = (2 ^ x₂ + 1) ^ 2 / (2 ^ x₂ * x₂) + 1 := hf x₂
  have h4 : f (-x₂) = (2 ^ (-x₂ : ℝ) + 1) ^ 2 / (2 ^ (-x₂ : ℝ) * (-x₂)) + 1 := hf (-x₂)

  have h5 : f x₂ + f (-x₂) = 2 := by
    rw [h3, h4]
    have h6 : x₂ ≠ 0 := by
      rcases mem_Ioc.mp hx₂ with  ⟨hx₂1, hx₂2⟩
      linarith
    have h7 : (2 : ℝ) ^ x₂ > 0 := by positivity
    have h8 : (2 : ℝ) ^ (-x₂ : ℝ) = 1 / ((2 : ℝ) ^ (x₂ : ℝ)) := by
      rw [Real.rpow_neg]
      all_goals
        norm_num
    have h9 : ((2 : ℝ) ^ (-x₂ : ℝ) + 1) ^ 2 / ((2 : ℝ) ^ (-x₂ : ℝ) * (-x₂)) =
        - ((2 ^ (x₂ : ℝ) + 1) ^ 2 / (2 ^ (x₂ : ℝ) * x₂)) := by
      rw [h8]
      field_simp [show x₂ ≠ 0 by exact h6, show (2 : ℝ) ^ x₂ ≠ 0 by positivity]
      <;> ring
    have h10 : ((2 : ℝ) ^ x₂ + 1) ^ 2 / ((2 : ℝ) ^ x₂ * x₂) + ((2 ^ (-x₂ : ℝ) + 1) ^ 2 / ((2 : ℝ) ^ (-x₂ : ℝ) * (-x₂)) ) = 0 := by
      rw [h9]
      all_goals
        ring
    linarith

  have h11 : f (-x₂) = 2 - N := by
    linarith [show f x₂ = N from by linarith [hx₂'], h5]

  have h13 : M + N ≥ 2 := by linarith [h11, h2]

  have h14 : -x₁ ∈ Ioc (0 : ℝ) (2018 : ℝ) := by
    rcases mem_Ico.mp hx₁ with ⟨hx₁1, hx₁2⟩
    constructor
    · linarith
    · linarith

  have h15 : f (-x₁) ≥ N := by
    apply hNlb
    exact h14

  have h17 : f x₁ = (2 ^ x₁ + 1) ^ 2 / (2 ^ x₁ * x₁) + 1 := hf x₁
  have h18 : f (-x₁) = (2 ^ (-x₁ : ℝ) + 1) ^ 2 / (2 ^ (-x₁ : ℝ) * (-x₁)) + 1 := hf (-x₁)

  have h19 : f x₁ + f (-x₁) = 2 := by
    rw [h17, h18]
    have h6 : x₁ ≠ 0 := by
      rcases mem_Ico.mp hx₁ with  ⟨hx₁1, hx₁2⟩
      linarith
    have h7 : (2 : ℝ) ^ x₁ > 0 := by positivity
    have h8 : (2 : ℝ) ^ (-x₁ : ℝ) = 1 / ((2 : ℝ) ^ (x₁ : ℝ)) := by
      rw [Real.rpow_neg]
      all_goals
        norm_num
    have h9 : ((2 : ℝ) ^ (-x₁ : ℝ) + 1) ^ 2 / ((2 : ℝ) ^ (-x₁ : ℝ) * (-x₁)) =
        - ((2 ^ (x₁ : ℝ) + 1) ^ 2 / (2 ^ (x₁ : ℝ) * x₁)) := by
      rw [h8]
      field_simp [show x₁ ≠ 0 by exact h6, show (2 : ℝ) ^ x₁ ≠ 0 by positivity]
      <;> ring
    have h10 : ((2 : ℝ) ^ x₁ + 1) ^ 2 / ((2 : ℝ) ^ x₁ * x₁) + ((2 ^ (-x₁ : ℝ) + 1) ^ 2 / ((2 : ℝ) ^ (-x₁ : ℝ) * (-x₁)) ) = 0 := by
      rw [h9]
      all_goals
        ring
    linarith

  have h20 : f (-x₁) = 2 - M := by
    linarith [show f x₁ = M from by linarith [hx₁'], h19]

  have h21 : M + N ≤ 2 := by linarith [h20, h15]

  linarith [h13, h21]