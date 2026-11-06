import Mathlib

theorem algebra_608243 :
    {x : ℝ | 0 < x ∧ 1 / 2 * (3 * x ^ 2 - 1) = (x ^ 2 - 50 * x - 10) * (x ^ 2 + 25 * x + 5)} = {25 + 2 * Real.sqrt 159} := by 
  ext x
  simp [-one_div]
  apply Iff.intro
  . -- Forward: if x is a positive solution, then x = 25 + 2 * sqrt 159
    rintro ⟨hx, h₀⟩
    let a := x ^ 2 - 50 * x - 10
    let b := x ^ 2 + 25 * x + 5
    rw [show x ^ 2 - 50 * x - 10 = a by rfl, show x ^ 2 + 25 * x + 5 = b by rfl, show 3 * x ^ 2 - 1 = a + 2 * b - 1 by ring] at h₀
    replace h₀ : (a - 1) * (2 * b - 1) = 0 := by
      ring_nf at h₀ ⊢
      linarith only [h₀]
    simp at h₀
    cases h₀ with
    | inl h₀ =>
      simp [a] at h₀
      have h₁ : x ^ 2 - 50 * x - 11 = 0 := by linarith only [h₀]
      have h₂ : (x - (25 + 2 * Real.sqrt 159)) * (x - (25 - 2 * Real.sqrt 159)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < 159 by norm_num), Real.mul_self_sqrt (show 0 ≤ 159 by norm_num), sq_nonneg (x - 25), Real.sqrt_nonneg 159, Real.sq_sqrt (show 0 ≤ 159 by norm_num)]
      simp at h₂
      cases h₂ with
      | inl h₂ =>
        linarith only [h₂]
      | inr h₂ =>
        nlinarith [Real.sqrt_pos.mpr (show 0 < 159 by norm_num), Real.mul_self_sqrt (show 0 ≤ 159 by norm_num), Real.sqrt_nonneg 159, Real.sq_sqrt (show (0 : ℝ) ≤ 159 by norm_num), Real.sqrt_nonneg 159]
    | inr h₀ =>
      simp [b] at h₀
      nlinarith [sq_nonneg (x + 25 / 2), sq_nonneg (x + 12.5)]
  . -- Reverse: x = 25 + 2 * sqrt 159 is a positive solution
    intro h₀
    rw [h₀]
    have hx1 : 0 < 25 + 2 * Real.sqrt 159 := by
      positivity
    constructor
    . -- Show that x is positive.
      linarith only [hx1]
    . -- Show the equation.
      have eq1 : (25 + 2 * Real.sqrt 159) ^ 2 = 1261 + 100 * Real.sqrt 159 := by
        calc
          (25 + 2 * Real.sqrt 159) ^ 2
            = 25 ^ 2 + 2 * (25) * (2 * Real.sqrt 159) + (2 * Real.sqrt 159) ^ 2 := by ring
          _ = 625 + 100 * Real.sqrt 159 + 4 * (Real.sqrt 159) ^ 2 := by ring
          _ = 625 + 100 * Real.sqrt 159 + 4 * 159 := by rw [Real.sq_sqrt (show 0 ≤ (159 : ℝ) by norm_num)]
          _ = 1261 + 100 * Real.sqrt 159 := by ring
      have eq₅ : 1 / 2 * (3 * (25 + 2 * Real.sqrt 159) ^ 2 - 1) = ( (25 + 2 * Real.sqrt 159) ^ 2 - 50 * (25 + 2 * Real.sqrt 159) - 10 ) * ( (25 + 2 * Real.sqrt 159) ^ 2 + 25 * (25 + 2 * Real.sqrt 159) + 5 ) := by
        rw [show (25 + 2 * Real.sqrt 159) ^ 2 = 1261 + 100 * Real.sqrt 159 by linarith [eq1]]
        field_simp
        nlinarith [ Real.sqrt_nonneg 159, Real.sq_sqrt (show 0 ≤ (159 : ℝ) by norm_num), sq_nonneg ( (25 + 2 * Real.sqrt 159) ^ 2 - 1261 - 100 * Real.sqrt 159 ), sq_nonneg ( (25 + 2 * Real.sqrt 159) ^ 2 ), sq_nonneg ( (25 + 2 * Real.sqrt 159) ) ]
      exact_mod_cast eq₅