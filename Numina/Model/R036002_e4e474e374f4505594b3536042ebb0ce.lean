import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_191171 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
  (f : ℝ → ℝ) (hf : f = λ x => x / (a * x ^ 2 + b)) :
  IsGreatest (range f) (1 / (2 * sqrt (a * b))) := by
  have h1 : ∀ x : ℝ, f x = x / (a * x ^ 2 + b) := by
    intro x
    rw [hf]
  have h2 : 1 / (2 * Real.sqrt (a * b)) ∈ range f := by
    use Real.sqrt b / Real.sqrt a
    have h3 : a * (Real.sqrt b / Real.sqrt a) ^ 2 + b = 2 * b := by
      have h4 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
      have h5 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
      have h4' : (Real.sqrt b / Real.sqrt a) ^ 2 = (Real.sqrt b ^ 2) / (Real.sqrt a ^ 2) := by
        field_simp
      rw [h4', h4, h5]
      <;> field_simp <;> nlinarith
    have h1' : f (Real.sqrt b / Real.sqrt a) = (Real.sqrt b / Real.sqrt a) / (a * (Real.sqrt b / Real.sqrt a) ^ 2 + b) := by 
      apply h1
    rw [h1']
    have h4 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
      rw [Real.sqrt_mul (by linarith)]
    have h6 : Real.sqrt a > 0 := by positivity
    have h7 : Real.sqrt b > 0 := by positivity
    have h8 : Real.sqrt (a * b) > 0 := by positivity
    have h5 : (Real.sqrt b / Real.sqrt a) / (a * (Real.sqrt b / Real.sqrt a) ^ 2 + b) = 1 / (2 * Real.sqrt (a * b)) := by 
      rw [h3]
      rw [h4]
      field_simp [show Real.sqrt a ≠ 0 by positivity, show Real.sqrt a ^ 2 = a by
        rw [Real.sq_sqrt]
        linarith
      , show Real.sqrt b ^ 2 = b by
        rw [Real.sq_sqrt]
        linarith
      ]
      <;> nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity)]
    linarith
  have h5 : ∀ y ∈ range f, y ≤ 1 / (2 * Real.sqrt (a * b)) := by
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1 x] at hx
    have h6 : 0 < a := ha
    have h7 : 0 < b := hb
    have h8 : a * x ^ 2 + b > 0 := by
      nlinarith [sq_nonneg x, h6, h7]
    have h9 : Real.sqrt (a * b) > 0 := by
      have h10 : 0 < a := ha
      have h11 : 0 < b := hb
      have h12 : a * b > 0 := mul_pos h10 h11
      positivity
    -- For all $x$ like in the term $f(x)$, prove it is less than or equal to $\lnot\frac{1}{2 \cdot \sqrt{\cdot \cdot \cdot}}$. Using fundamental ineq. reasoning.
    have h10 : x / (a * x ^ 2 + b) ≤ 1 / (2 * Real.sqrt (a * b)) := by
      -- Assume cross multiply operation as rewrite or transformation rule.
      -- Use positivity definition.
      have h11 : 0 < a * x ^ 2 + b := h8
      have h12 : 0 < 2 * Real.sqrt (a * b) := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < a * b by positivity), Real.sqrt_nonneg (a * b)]
      -- Multiply both sides, swapping <= and > so that main goal uses equality denominators match multiplier.
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      -- Apply fundamental nonnegativity.
      -- by linarith [sq_nonneg (a * x - Real.sqrt (a * b)), sq_nonneg ((Real.sqrt a)*x - Real.sqrt b)]
      have h13 : a * x ^ 2 + b ≥ 2 * x * Real.sqrt (a * b) := by
        nlinarith [sq_nonneg (x * Real.sqrt a - Real.sqrt b), sq_nonneg (x * a - Real.sqrt (a * b)), sq_nonneg (x * Real.sqrt a - Real.sqrt b), sq_nonneg ((Real.sqrt a) * x - Real.sqrt b), sq_nonneg (x * (Real.sqrt a) ^ 2 - (Real.sqrt b) * (Real.sqrt a) ^ 2), 
          Real.sqrt_nonneg (a * b), 
          Real.sqrt_nonneg a, Real.sqrt_nonneg b, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a * b) by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), 
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
          sq_nonneg (Real.sqrt a * x - Real.sqrt b), 
          mul_pos ha hb, 
          mul_nonneg (show (0 : ℝ) ≤ x ^ 2 by positivity) (show (0 : ℝ) ≤ a by linarith), 
          mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb), 
          mul_nonneg (Real.sqrt_nonneg a) (show (0 : ℝ) ≤ x ^ 2 by positivity)
        ]
      nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg b, Real.sqrt_nonneg a, sq_nonneg (x * a - Real.sqrt (a * b)), sq_nonneg (x * Real.sqrt a - Real.sqrt b), sq_nonneg ((Real.sqrt a) * x - Real.sqrt b), sq_nonneg (x * Real.sqrt a - Real.sqrt b), sq_nonneg (x * Real.sqrt a), sq_nonneg (x), sq_nonneg (Real.sqrt a * x - Real.sqrt b), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity)]
    have h11 : y = x / (a * x ^ 2 + b) := by
      linarith [hx]
    linarith [h10, h11]

  constructor
  · -- Show that 1/(2 * sqrt(a * b)) is in the range of f
    exact h2
  · -- Show that 1/(2 * sqrt(a * b)) is the greatest value in the range of f
    intro y hy
    have h9 : y ∈ range f := by
      simpa using hy
    have h10 : y ≤ 1 / (2 * Real.sqrt (a * b)) := h5 y h9
    linarith