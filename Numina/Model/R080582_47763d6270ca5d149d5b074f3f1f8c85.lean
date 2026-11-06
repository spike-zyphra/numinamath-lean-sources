import Mathlib

theorem algebra_304037 :
    IsGreatest {x * a + y * b | (x : ℝ) (y : ℝ) (a : ℝ) (b : ℝ)
      (h₀ : x ^ 2 + y ^ 2 = 1) (h₁ : a ^ 2 + b ^ 2 = 25)} 5 := by 
  constructor
  · -- Show that 5 is achievable in the set
    use 1, 0, 5, 0
    norm_num
  · -- Show that 5 is the maximum value of all elements in the set
    intro r hr
    rcases hr with ⟨x, y, a, b, h₀, h₁, h_eq⟩
    have h : x * a + y * b ≤ 5 := by
      have h1 : (x * a + y * b) ^ 2 ≤ (x ^ 2 + y ^ 2) * (a ^ 2 + b ^ 2) := by
        nlinarith [sq_nonneg (x * b - y * a)]
      rw [h₀, h₁] at h1
      nlinarith [sq_nonneg (x * a + y * b), h1]
    linarith [h_eq, h]