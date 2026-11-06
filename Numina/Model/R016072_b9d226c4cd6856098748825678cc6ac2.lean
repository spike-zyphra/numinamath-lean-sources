import Mathlib

theorem algebra_293892 {a b : ℝ} (x : ℕ → ℝ) (h₀ : ∀ n, x (n + 1) = x n - x (n - 1))
    (h₁ : x 1 = a) (h₂ : x 2 = b) :
    x 100 = -a ∧ ∑ i in Finset.range 100, x (i + 1) = 2 * b - a := by
  -- Let's derive the value of x 0 from the recurrence relations
  have hx0 : x 0 = a - b := by 
    have eq0 : x 2 = x 1 - x 0 := h₀ 1
    rw [h₁, h₂] at eq0
    linarith

  -- Let's compute x 3 to x 7 to identify the cycle
  have h3 : x 1 = a := h₁
  have h4 : x 2 = b := h₂
  have h5 : x 3 = x 2 - x 1 := h₀ 2
  rw [h3, h4] at h5
  -- So now h5 is x_3 = b - a

  have h6 : x 4 = x 3 - x 2 := h₀ 3
  rw [show x 3 = b - a by linarith, h4] at h6
  -- So h6 is x_4 = -a

  have h7 : x 5 = x 4 - x 3 := h₀ 4
  rw [show x 4 = -a by linarith, show x 3 = b - a by linarith] at h7
  -- So h7 is x_5 = -b

  have h8 : x 6 = x 5 - x 4 := h₀ 5
  rw [show x 5 = -b by linarith, show x 4 = -a by linarith] at h8
  -- So h8 is x_6 = a - b

  have h9 : x 7 = x 6 - x 5 := h₀ 6
  rw [show x 6 = a - b by linarith, show x 5 = -b by linarith] at h9
  -- So h9 is x_7 = a

  have h10 : x 8 = x 7 - x 6 := h₀ 7
  rw [show x 7 = a by linarith, show x 6 = a - b by linarith] at h10
  -- So h10 is x_8 = b

  -- Prove that x 100 = -a
  have hx100 : x 100 = -a := by
    norm_num [h₀, h₁, h₂, hx0] at *
    <;> linarith

  -- Prove that the sum S_100 = 2 * b - a
  have hsum : ∑ i in Finset.range 100, x (i + 1) = 2 * b - a := by
    norm_num [Finset.sum_range_succ, h₀, h₁, h₂, hx0] at *
    <;> linarith

  -- The final result
  constructor 
  · -- First part: x_100 = -a
    exact hx100 
  · -- Second part: ∑ i in Finset.range 100, x (i + 1) = 2 * b - a
    exact hsum