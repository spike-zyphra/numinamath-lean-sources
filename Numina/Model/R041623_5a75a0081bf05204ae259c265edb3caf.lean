import Mathlib

open Real


theorem algebra_605937 (a b c : ℝ) (h1 : 0 ≤ a) (h2 : a ≤ b) (h3 : b ≤ c) (h4 : a + b + c = 1) :
a * b * √(b - a) + b * c * √(c - b) + a * c * √(c - a) < 1 / 4 := by
  have h5 : ∀ x y : ℝ, x ≤ y → √(y - x) ≤ (1 + y - x) / 2:= by
    intro x y hxy
    have h6 : √(y - x) ≤ (1 + y - x) / 2:= by
      have h7 : (√(y - x) : ℝ) ^ 2 = y - x := by
        rw [Real.sq_sqrt]
        nlinarith
      have h8 : (( (1 + y - x) / 2 : ℝ ) ) ^ 2 ≥ y - x := by
        nlinarith [sq_nonneg ( (y - x) - 1 ) ]
      have h9 : ( (√(y - x)) ) ≤ ( (1 + y - x) / 2 ) := by
        nlinarith [Real.sqrt_nonneg (y - x), sq_nonneg ( (√(y - x)) - ( (1 + y - x) / 2 ) ) ]
      nlinarith
    linarith
  have h6 : a * b * √(b - a) ≤ a * b * ((1 + b - a) / 2) := by
    have h32 : √(b - a) ≤ (1 + b - a) / 2 := by
      apply h5 a b
      linarith
    have h33 : a * b ≥ 0 := by
      nlinarith
    nlinarith [h32, Real.sqrt_nonneg (b - a)]
  have h7 : b * c * √(c - b) ≤ b * c * ((1 + c - b) / 2) := by
    have h32 : √(c - b) ≤ (1 + c - b) / 2 := by
      apply h5 b c
      linarith
    have h33 : b * c ≥ 0 := by
      nlinarith
    nlinarith [h32, Real.sqrt_nonneg (c - b)]
  have h8 : a * c * √(c - a) ≤ a * c * ((1 + c - a) / 2) := by
    have h32 : √(c - a) ≤ (1 + c - a) / 2 := by
      have h70 : a ≤ c := by linarith
      apply h5 a c
      linarith
    have h33 : a * c ≥ 0 := by
      nlinarith
    nlinarith [h32, Real.sqrt_nonneg (c - a)]
  have h9 : a * b * √(b - a) + b * c * √(c - b) + a * c * √(c - a) ≤
      a * b * ((1 + b - a) / 2) + b * c * ((1 + c - b) / 2) + a * c * ((1 + c - a) / 2) := by
    linarith [h6, h7, h8]
  have h10 : a * b * ((1 + b - a) / 2) + b * c * ((1 + c - b) / 2) + a * c * ((1 + c - a) / 2) < 1 / 4 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4), sq_nonneg (c - 1 / 4),
      mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b - a by linarith),
      mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c - b by linarith),
      mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c - a by linarith)
    ]
  linarith [h9, h10]