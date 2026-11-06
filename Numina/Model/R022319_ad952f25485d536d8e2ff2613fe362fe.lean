import Mathlib

open BigOperators Real Set

theorem inequalities_272224 (f : ℝ → ℝ → ℝ → ℝ → ℝ)
  (h₀ : ∀ a b c d, f a b c d = (1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a)))
  (h₁ : 0 < d) (h₂ : d ≤ c) (h₃ : c ≤ b) (h₄ : b ≤ a) :
  IsLeast {x | ∃ a b c d, 0 < d ∧ d ≤ c ∧ c ≤ b ∧ b ≤ a ∧ f a b c d = x} ((3 / 2) ^ 4) := by
  constructor
  · -- Show that (3/2)^4 is in the set
    use 1, 1, 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    rw [h₀ 1 1 1 1]
    norm_num
  · -- Show that (3/2)^4 is the minimum
    intro x hx
    rcases hx with ⟨a, b, c, d, h1, h2, h3, h4, h_eq⟩
    have h5 : f a b c d = (1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a)) := by
      apply h₀
    rw [h5] at h_eq
    have h7 : 0 < a := by linarith
    have h8 : 0 < b := by linarith
    have h9 : 0 < c := by linarith
    have h10 : (1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a)) ≥ (3 / 2) ^ 4 := by
      have h12 : (1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a)) - (3 / 2) ^ 4 ≥ 0 := by
        have h11 : 0 < (a + b) * (b + c) * (c + d) * (d + a) := by positivity
        have h13 : (1 + c / (a + b)) * (1 + d / (b + c)) * (1 + a / (c + d)) * (1 + b / (d + a)) - (3 / 2) ^ 4 =
            ((2 * (a + b) + 2 * c) * (2 * (b + c) + 2 * d) * (2 * (c + d) + 2 * a) * (2 * (d + a) + 2 * b) - 81 * (a + b) * (b + c) * (c + d) * (d + a)) / (16 * (a + b) * (b + c) * (c + d) * (d + a)) := by
          field_simp
          ring
        rw [h13]
        have h14 : ((2 * (a + b) + 2 * c) * (2 * (b + c) + 2 * d) * (2 * (c + d) + 2 * a) * (2 * (d + a) + 2 * b) - 81 * (a + b) * (b + c) * (c + d) * (d + a)) ≥ 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
            sq_nonneg (a + b - c - d), sq_nonneg (a + d - b - c),
            mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ b - c by linarith),
            mul_nonneg (show 0 ≤ b - c by linarith) (show 0 ≤ c - d by linarith),
            mul_nonneg (show 0 ≤ c - d by linarith) (show 0 ≤ d by linarith),
            mul_nonneg (show 0 ≤ b - c by linarith) (show 0 ≤ d by linarith),
            mul_nonneg (show 0 ≤ a - c by linarith) (show 0 ≤ c - d by linarith),
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ d by linarith),
            mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ d by linarith),
            mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ d by linarith),
            mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ c by linarith),
            mul_nonneg (show 0 ≤ a - c by linarith) (show 0 ≤ b by linarith)
          ]
        have h15 : ((2 * (a + b) + 2 * c) * (2 * (b + c) + 2 * d) * (2 * (c + d) + 2 * a) * (2 * (d + a) + 2 * b) - 81 * (a + b) * (b + c) * (c + d) * (d + a)) / (16 * (a + b) * (b + c) * (c + d) * (d + a)) ≥ 0 := by
          apply div_nonneg
          linarith
          all_goals positivity
        linarith
      linarith
    have h11 : x ≥ (3 / 2) ^ 4 := by
      linarith [h_eq, h10]
    linarith