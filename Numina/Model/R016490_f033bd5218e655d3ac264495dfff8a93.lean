import Mathlib

theorem algebra_305637 (a : ℝ) (ha : ∀ x ∈ Set.Icc 0 1, -x^2 + a * x - a / 4 + (1 / 2) ≤ 2)
    (hmax : ∃ x ∈ Set.Icc 0 1, -x^2 + a * x - a / 4 + (1 / 2) = 2) :
    a = -6 ∨ a = 10 / 3 := by
  rcases hmax with ⟨x, hx, heq⟩
  have h1 : 0 ≤ x := by
    have h1 : x ∈ Set.Icc (0 : ℝ) (1 : ℝ) := hx
    exact h1.left
  have h2 : x ≤ 1 := by
    have h1 : x ∈ Set.Icc (0 : ℝ) (1 : ℝ) := hx
    exact h1.right
  have h3 := ha 0 (by norm_num)
  have h4 := ha 1 (by norm_num)
  have h5 : -x^2 + a * x - a / 4 + (1 / 2) = 2 := heq
  have h6 : (x) ^ 2 - a * x + a / 4 = -3 / 2 := by 
    nlinarith
  have h7 : (a : ℝ) ^ 2 - 4 * (a / 4 + 3 / 2) ≥ 0 := by 
    nlinarith [sq_nonneg (x - a / 2), sq_nonneg (x - 1), sq_nonneg (x - 0), 
      mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ 1 - x by linarith)]
  have h8 : (a - 3) * (a + 2) ≥ 0 := by 
    nlinarith
  by_cases h9 : a ≥ 3
  · -- Assume a ≥ 3, so a = 10/3
    have h10 : a ≤ 10 / 3 := by 
      nlinarith
    have h11 : a = 10 / 3 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (a - 10 / 3), 
        mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ 1 - x by linarith)
      ]
    right
    linarith
  · -- Assume a < 3
    have h10 : a ≤ -2 := by 
      nlinarith
    have h11 : a = -6 := by 
      nlinarith [sq_nonneg (x - 0), sq_nonneg (a + 6), 
        mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ 1 - x by linarith)
      ]
    left
    linarith