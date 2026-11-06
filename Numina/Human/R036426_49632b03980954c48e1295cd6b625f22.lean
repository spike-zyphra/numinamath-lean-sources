import Mathlib

/- Determine the largest positive integer $n$ such that there exist positive integers $x, y, z$ so that

$$
n^{2}=x^{2}+y^{2}+z^{2}+2 x y+2 y z+2 z x+3 x+3 y+3 z-6
$$ -/
theorem algebra_608168 :
    IsGreatest {n : ℤ | n > 0 ∧ ∃ x y z : ℤ, x > 0 ∧ y > 0 ∧ z > 0 ∧ n ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * x * y + 2 * y * z + 2 * z * x + 3 * x + 3 * y + 3 * z - 6} 8 := by
  constructor
  -- First, we show that n = 8 is possible
  -- We can take x = 1, y = 1, z = 5
  . use by simp, 1, 1, 5
    simp
  -- Next, we show that any such n must be ≤ 8
  . intro n ⟨hn, x, y, z, hx, hy, hz, h⟩
    -- Let r = x + y + z + 1 ≥ 4
    let r := x + y + z + 1
    -- Then the equation becomes n^2 = r^2 + r - 8
    replace h : n ^ 2 = r ^ 2 + r - 8 := by linear_combination h
    have h₀ : r >= 4 := by simp only [r]; linarith
    clear_value r
    -- r ≤ 8 implies n ≤ 8, so we only need to exclude r > 8
    suffices H : r ≤ 8 by nlinarith
    by_contra! H
    -- If r > 8, then r^2 + r - 8 ∈ (r^2, (r+1)^2)
    have h₁ : r ^ 2 < r ^ 2 + r - 8 := by linarith only [H]
    have h₂ : r ^ 2 + r - 8 < (r + 1) ^ 2 := by linarith only [H]
    rw [← h] at h₁ h₂
    -- So n ∈ (r, r+1), which is a contradiction
    rw [sq_lt_sq₀ (by linarith) (by linarith)] at h₁ h₂
    linarith only [h₁, h₂]
