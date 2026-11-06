import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_90414 {α γ : ℂ} (f : ℂ → ℂ)
  (h₀ : ∀ z, f z = (4 + Complex.I) * z ^ 2 + α * z + γ)
  (h₁ : ∃ r : ℝ, f 1 = r) (h₂ : ∃ r : ℝ, f Complex.I = r) :
  abs α + abs γ ≥ Real.sqrt 2 := by
  rcases h₁ with ⟨r₁, hr₁⟩
  rcases h₂ with ⟨r₂, hr₂⟩
  have h1 : f 1 = (4 + Complex.I) * 1 ^ 2 + α * 1 + γ := h₀ 1
  have h2 : f Complex.I = (4 + Complex.I) * Complex.I ^ 2 + α * Complex.I + γ := h₀ Complex.I
  rw [h1] at hr₁
  rw [h2] at hr₂
  simp [pow_two, Complex.ext_iff] at hr₁ hr₂
  ring_nf at hr₁ hr₂
  have eq1 : α.im + γ.im = -1 := by
    nlinarith
  have eq2 : α.re + γ.im = 1 := by
    nlinarith
  have eq3 : α.im = α.re - 2 := by
    linarith
  have eq4 : γ.im = 1 - α.re := by
    linarith
  have eq5 : abs α = Real.sqrt (α.re ^ 2 + α.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  have eq6 : abs γ = Real.sqrt (γ.re ^ 2 + γ.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [eq5, eq6]
  have h4 : (α.re) ^ 2 + (α.im) ^ 2 ≥ 0 := by nlinarith
  have h5 : (γ.re) ^ 2 + (γ.im) ^ 2 ≥ 0 := by nlinarith
  have h8 : (α.re) ^ 2 + (α.im) ^ 2 = (α.re) ^ 2 + (α.re - 2) ^ 2 := by
    rw [eq3]
  have h9 : (γ.re) ^ 2 + (γ.im) ^ 2 = (γ.re) ^ 2 + (1 - α.re) ^ 2 := by
    rw [eq4]
  rw [h8, h9]
  have h10 : Real.sqrt ((α.re) ^ 2 + (α.re - 2) ^ 2) + Real.sqrt ((γ.re) ^ 2 + (1 - α.re) ^ 2) ≥ Real.sqrt 2 := by
    have h11 : (Real.sqrt ((α.re) ^ 2 + (α.re - 2) ^ 2) + Real.sqrt ((γ.re) ^ 2 + (1 - α.re) ^ 2)) ^ 2 ≥ 2 := by
      have h12 : (Real.sqrt ((α.re) ^ 2 + (α.re - 2) ^ 2) + Real.sqrt ((γ.re) ^ 2 + (1 - α.re) ^ 2)) ^ 2 = (Real.sqrt ((α.re) ^ 2 + (α.re - 2) ^ 2) ^2) + (Real.sqrt ((γ.re) ^ 2 + (1 - α.re) ^ 2) ^2) + 2 * (Real.sqrt ((α.re) ^ 2 + (α.re - 2) ^ 2) * Real.sqrt ((γ.re) ^ 2 + (1 - α.re) ^ 2)) := by
        ring
      rw [h12]
      have h13 : Real.sqrt ((α.re) ^ 2 + (α.re - 2) ^ 2) ^ 2 = (α.re) ^ 2 + (α.re - 2) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      have h14 : Real.sqrt ((γ.re) ^ 2 + (1 - α.re) ^ 2) ^ 2 = (γ.re) ^ 2 + (1 - α.re) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      rw [h13, h14]
      nlinarith [sq_nonneg (α.re - 1), sq_nonneg (γ.re), 
        sq_nonneg (Real.sqrt ((α.re) ^ 2 + (α.re - 2) ^ 2) - Real.sqrt ((γ.re) ^ 2 + (1 - α.re) ^ 2)), 
        Real.sqrt_nonneg ((α.re) ^ 2 + (α.re - 2) ^ 2), 
        Real.sqrt_nonneg ((γ.re) ^ 2 + (1 - α.re) ^ 2), 
        mul_nonneg (Real.sqrt_nonneg ((α.re) ^ 2 + (α.re - 2) ^ 2)) (Real.sqrt_nonneg ((γ.re) ^ 2 + (1 - α.re) ^ 2)), 
        sq_nonneg (α.re -1 ), sq_nonneg (γ.re - 0 )
      ]
    have h14 : Real.sqrt ((α.re) ^ 2 + (α.re - 2) ^ 2) + Real.sqrt ((γ.re) ^ 2 + (1 - α.re) ^ 2) ≥ 0 := by
      positivity
    have h15 : (Real.sqrt ((α.re) ^ 2 + (α.re - 2) ^ 2) + Real.sqrt ((γ.re) ^ 2 + (1 - α.re) ^ 2))^2 ≥ 2 := h11
    nlinarith [show 0 ≤ Real.sqrt ((α.re) ^ 2 + (α.re - 2) ^ 2) + Real.sqrt ((γ.re) ^ 2 + (1 - α.re) ^ 2) by positivity, 
      Real.sqrt_nonneg (2), 
      Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    ]
  nlinarith