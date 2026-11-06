import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_597146 :
  IsLeast {x : ℝ | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = c / (a + b) + a / (b + c) + b / (c + a)} (3 / 2) := by
  constructor
  · -- Show 3/2 is in the set
    use 1, 1, 1
    norm_num
  · -- Show 3/2 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hx_eq⟩
    have h : c / (a + b) + a / (b + c) + b / (c + a) ≥ 3 / 2 := by
      have h2 : a + b > 0 := by linarith
      have h3 : b + c > 0 := by linarith
      have h4 : c + a > 0 := by linarith
      have h5 : c / (a + b) + a / (b + c) + b / (c + a) - 3 / 2 ≥ 0 := by
        have hn : (c * (b + c) * (c + a) + a * (a + b) * (c + a) + b * (a + b) * (b + c) - 3 / 2 * (a + b) * (b + c) * (c + a)) ≥ 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
            mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith),
            mul_pos (show (0 : ℝ) < b by linarith) (show (0 : ℝ) < c by linarith),
            mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < c by linarith)]
        have h6 : (a + b) * (b + c) * (c + a) > 0 := by positivity
        have h_eq : c / (a + b) + a / (b + c) + b / (c + a) - 3 / 2 =
          (c * (b + c) * (c + a) + a * (a + b) * (c + a) + b * (a + b) * (b + c) - 3 / 2 * (a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a)) := by
          field_simp
          <;> ring_nf <;> field_simp
          <;> ring
        rw [h_eq]
        apply div_nonneg hn (by positivity)
      linarith
    linarith [h, hx_eq]