import Mathlib

open Real

theorem algebra_2303
  (a : ℕ → ℝ)
  (h₀ : a 1 = 1 / (Real.sqrt 2 - 1))
  (h₁ : ∀ n ≥ 2, a n = 1 / a (n - 1)) :
  a 2015 = Real.sqrt 2 + 1 := by
  have ha1 : a 1 = Real.sqrt 2 + 1 := by
    rw [h₀]
    have h1 : 0 < (Real.sqrt 2 : ℝ) := by
      have h2 : 0 < (Real.sqrt 2 : ℝ) := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
      linarith
    have h2 : Real.sqrt 2 - 1 > 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), h1]
    field_simp [h2]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  -- by induction, we can prove that for all odd n, a(n) = sqrt 2 +1
  have ha2 : ∀ n, a (2 * n + 1) = Real.sqrt 2 + 1 := by
    intro n
    induction n with
    | zero =>
      simp [ha1]
    | succ n ih =>
      have h3 : a (2 * n + 1) = Real.sqrt 2 + 1 := ih
      have h2n2 : a (2 * n + 2) = 1 / a (2 * n + 1) := by
        specialize h₁ (2 * n + 2) (by linarith)
        simpa using h₁
      have h_eq1 : a (2 * n + 2) = Real.sqrt 2 - 1 := by
        rw [h2n2, h3]
        field_simp [(show Real.sqrt 2 + 1 > 0 by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        )]
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      -- for $a_{2n+3}$:
      have h2n3' : a (2 * (n + 1) + 1) = 1 / a (2 * n + 2) := by
        specialize h₁ (2 * (n + 1) + 1) (by ring_nf; omega)
        simpa using h₁
      rw [h2n3']
      rw [h_eq1]
      have h1 : 0 < (Real.sqrt 2 : ℝ) := by
        have h2 : 0 < (Real.sqrt 2 : ℝ) := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
        linarith
      have h2 : Real.sqrt 2 - 1 > 0 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), h1]
      field_simp [h2]
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h2015 : 2015 = 2 * 1007 + 1 := by
    omega
  rw [h2015]
  apply ha2 1007