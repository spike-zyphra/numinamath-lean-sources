import Mathlib
/-Find all values of $b$ for which the equations $1988x^2 + bx + 8891 = 0$ and $8891x^2 + bx + 1988 = 0$ have a common root.

Enter all the possible values of $b,$ separated by commas.-/
theorem algebra_2656 (b : ℝ) :
    (∃ x, 1988 * x ^ 2 + b * x + 8891 = 0 ∧ 8891 * x ^ 2 + b * x + 1988 = 0) ↔
    b = 10879 ∨ b = - 10879 := by 
  constructor
  · intro ⟨r, hr⟩ -- Let r be a common root
    have e₁ : (0 : ℝ) - 0 = 0 := by simp
    nth_rw 1 [← hr.2] at e₁
    nth_rw 1 [← hr.1] at e₁
    -- Substract these equations
    have e₂ : 8891 * r ^ 2 + b * r + 1988 - (1988 * r ^ 2 + b * r + 8891) = 6903 * (r ^ 2 - 1) := by ring
    rw [e₂] at e₁
    -- Simplify 
    rcases mul_eq_zero.mp e₁ with h | h
    · norm_num at h
    have : r ^ 2 - 1 = (r + 1) * (r - 1) := by ring
    rw [this] at h
    rcases mul_eq_zero.mp h with h₁ | h₁ -- Solve the equation about r and substitute
    · rw [← sub_neg_eq_add, sub_eq_zero] at h₁
      rw [h₁] at hr
      have : 1988 * (-1) ^ 2 + b * -1 + 8891 = 10879 - b := by ring
      rw [this] at hr
      left
      exact (sub_eq_zero.mp hr.1).symm
    rw [sub_eq_zero] at h₁
    rw [h₁] at hr
    have : 1988 * 1 ^ 2 + b * 1 + 8891 = b - -10879 := by ring
    rw [this] at hr
    right
    exact sub_eq_zero.mp hr.1
  intro h
  rcases h with h | h
  · use -1
    rw [h]
    constructor <;> ring
  use 1
  rw [h]
  constructor <;> ring
