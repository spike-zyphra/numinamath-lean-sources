import Mathlib

open Polynomial
theorem algebra_100581 (α β γ : ℝ) (h1 : α + β + γ = 14) (h2 : α^2 + β^2 + γ^2 = 84) (h3 : α^3 + β^3 + γ^3 = 584) :
    max (max α β) γ = 8 := by
  have h4 : α * β + β * γ + γ * α = 56 := by
    have eq1 : (α + β + γ) ^ 2 = α^2 + β^2 + γ^2 + 2 * (α * β + β * γ + γ * α) := by ring
    rw [h1, h2] at eq1
    linarith
  have h5 : α * β * γ = 64 := by
    have eq1 : α^3 + β^3 + γ^3 = (α + β + γ) ^3 - 3 * (α + β + γ) * (α * β + β * γ + γ * α) + 3 * (α * β * γ) := by ring
    rw [h1, h4] at eq1
    linarith
  have h6 : (α - 2) * (α - 4) * (α - 8) = 0 := by
    nlinarith [sq_nonneg (α - 2), sq_nonneg (α - 4), sq_nonneg (α - 8), sq_nonneg (β - 2), sq_nonneg (β - 4), sq_nonneg (β - 8), sq_nonneg (γ - 2), sq_nonneg (γ - 4), sq_nonneg (γ - 8)]
  have h6' : (α = 2 ∨ α = 4 ∨ α = 8) := by
    cases (mul_eq_zero.mp h6) with
    | inl h7 =>
      cases (mul_eq_zero.mp h7) with
      | inl h8 =>
        left
        linarith
      | inr h9 =>
        right
        left
        linarith
    | inr h10 =>
      right
      right
      linarith
  rcases h6' with (ha1 | ha2 | ha3)
  · -- $\alpha = 2$
    have h7 : β + γ = 12 := by
      linarith
    have h8 : β * γ = 32 := by
      have h8 : α * (β * γ) = 64 := by
        linarith [h5]
      rw [show α = 2 by linarith] at h8
      linarith
    have h11 : (β - 4) * (β - 8) = 0 := by
      nlinarith [sq_nonneg (β - 4), sq_nonneg (β - 8), h8, h7]
    cases (mul_eq_zero.mp h11) with
    | inl h12 =>
      have hb : β = 4 := by linarith
      have hg : γ = 8 := by linarith
      rw [ha1, hb, hg]
      norm_num [max_eq_right, max_eq_left]
    | inr h13 =>
      have hb : β = 8 := by linarith
      have hg : γ = 4 := by linarith
      rw [ha1, hb, hg]
      norm_num [max_eq_right, max_eq_left]
  · -- $\alpha = 4$
    have h7 : β + γ = 10 := by
      linarith
    have h8 : β * γ = 16 := by
      have h8 : α * (β * γ) = 64 := by
        linarith [h5]
      rw [show α = 4 by linarith] at h8
      linarith
    have h11 : (β - 2) * (β - 8) = 0 := by
      nlinarith [sq_nonneg (β - 2), sq_nonneg (β - 8), h8, h7]
    cases (mul_eq_zero.mp h11) with
    | inl h12 =>
      have hb : β = 2 := by linarith
      have hg : γ = 8 := by linarith
      rw [ha2, hb, hg]
      norm_num [max_eq_right, max_eq_left]
    | inr h13 =>
      have hb : β = 8 := by linarith
      have hg : γ = 2 := by linarith
      rw [ha2, hb, hg]
      norm_num [max_eq_right, max_eq_left]
  · -- $\alpha = 8$
    have h7 : β + γ = 6 := by
      linarith
    have h8 : β * γ = 8 := by
      have h8 : α * (β * γ) = 64 := by
        linarith [h5]
      rw [show α = 8 by linarith] at h8
      linarith
    have h11 : (β - 2) * (β - 4) = 0 := by
      nlinarith [sq_nonneg (β - 2), sq_nonneg (β - 4), h8, h7]
    cases (mul_eq_zero.mp h11) with
    | inl h12 =>
      have hb : β = 2 := by linarith
      have hg : γ = 4 := by linarith
      rw [ha3, hb, hg]
      norm_num [max_eq_right, max_eq_left]
    | inr h13 =>
      have hb : β = 4 := by linarith
      have hg : γ = 2 := by linarith
      rw [ha3, hb, hg]
      norm_num [max_eq_right, max_eq_left]