import Mathlib
open Real
/- Example 6 Given that $a, b, c$ are all real numbers, and $a > 100$. Prove: There are at most two integers $x$ such that
$$
\left|a x^{2}+b x+c\right| \leqslant 50 \text{. }
$$
(1991, Jiangsu Province Mathematics Summer Camp) -/
theorem algebra_325489 (a b c : ℝ) (ha : a > 100) : Set.ncard {x : ℤ | |a * x ^ 2 + b * x + c| ≤ 50} ≤ 2:= by
  -- Proof by contradiction
  by_contra H
  simp at H
  -- If the statement is false, then there are at least 3 integers satisfying the condition
  replace H : 3 ≤ Set.ncard {x : ℤ | |a * x ^ 2 + b * x + c| ≤ 50}:= by exact H
  -- There exists a subset with exactly 3 elements
  apply Set.exists_subset_card_eq at H
  rcases H with ⟨t, ht1, ht2⟩
  -- Extract the fact that t has exactly 3 elements
  apply Set.ncard_eq_three.1 at ht2
  -- Get the three distinct integers x, y, z from set t
  rcases ht2 with ⟨x, y, z, h1, h2, h3, h4⟩
  subst t
  -- Prove that x, y, z are in the set {x, y, z}
  have g1 : x ∈ ({x, y, z} : Set ℤ):= by simp
  have g2 : y ∈ ({x, y, z} : Set ℤ):= by simp
  have g3 : z ∈ ({x, y, z} : Set ℤ):= by simp
  -- Show that x, y, z satisfy the original condition |ax² + bx + c| ≤ 50
  replace g1 : x ∈ {x : ℤ | |a * x ^ 2 + b * x + c| ≤ 50}:= by exact ht1 g1
  replace g2 : y ∈ {x : ℤ | |a * x ^ 2 + b * x + c| ≤ 50}:= by exact ht1 g2
  replace g3 : z ∈ {x : ℤ | |a * x ^ 2 + b * x + c| ≤ 50}:= by exact ht1 g3
  simp at g1 g2 g3
  -- Since x, y, z are distinct, they must have some ordering
  replace h1 : x < y ∨ x > y:= by exact Int.ne_iff_lt_or_gt.mp h1
  replace h2 : x < z ∨ x > z:= by exact Int.ne_iff_lt_or_gt.mp h2
  replace h3 : y < z ∨ y > z:= by exact Int.ne_iff_lt_or_gt.mp h3
  -- Enumerate all possible orderings of x, y, z
  have g : x < y ∧ y < z ∨ x < z ∧ z < y ∨ y < x ∧ x < z ∨ y < z ∧ z < x ∨ z < x ∧ x < y ∨ z < y ∧ y < x:= by
    rcases h1 with h1 | h1
    all_goals
      rcases h2 with h2 | h2
      all_goals
        rcases h3 with h3 | h3
        any_goals
          try
            linarith
        all_goals
          aesop
  clear ht1
  -- Key lemma: For any three integers x > y > z satisfying the condition, we'll derive a contradiction
  have h4 : ∀ x y z : ℤ, x > y → y > z → |a * ↑x ^ 2 + b * ↑x + c| ≤ 50 → |a * ↑y ^ 2 + b * ↑y + c| ≤ 50 → |a * ↑z ^ 2 + b * ↑z + c| ≤ 50 → False := by
    intro x y z hx hy h1 h2 h3
    -- Case analysis based on whether y is greater than or equal to the vertex of the parabola (-b/2a)
    by_cases hz : y ≥ -b / (2 * a)
    .
      -- Case 1: y ≥ -b/2a (y is to the right of or at the vertex)
      have h4 : a * (x + y) + b > 100:= by
        replace hx : x + y ≥ 2 * y + 1:= by omega
        have g4 : 2 * a * y ≥ (2 * a) * (-b / (2 * a)):= by
          have g4 : 2 * a ≥ 0:= by linarith
          exact mul_le_mul_of_nonneg_left hz g4
        rify at hx
        replace hx : a * (2 * y + 1) ≤ a * (x + y):= by
          have g5 : a ≥ 0:= by linarith
          exact mul_le_mul_of_nonneg_left hx g5
        rw [show 2 * a * (-b / (2 * a)) = -b by field_simp ; linarith] at g4
        linarith
      -- Show that the difference between f(x) and f(y) is greater than 100
      have h5 : |a * ↑x ^ 2 + b * ↑x + c - (a * ↑y ^ 2 + b * ↑y + c)| > 100:= by
        rw [show a * ↑x ^ 2 + b * ↑x + c - (a * ↑y ^ 2 + b * ↑y + c) = (a * (x + y) + b) * (x - y) by ring]
        rw [show |(a * (x + y) + b) * (x - y)| = |a * (x + y) + b| * |(↑x : ℝ) - y| by exact abs_mul (a * (↑x + ↑y) + b) (↑x - ↑y)]
        have g5 : |x - y| ≥ 1:= by
          by_contra H
          simp at H
          linarith
        rify at g5
        replace g5 : |a * (↑x + ↑y) + b| * |(↑x : ℝ) - ↑y| ≥ |a * (↑x + ↑y) + b| * 1:= by
          have g6 : |a * (↑x + ↑y) + b| ≥ 0:= by positivity
          exact mul_le_mul_of_nonneg_left g5 g6
        rw [show a * (↑x + ↑y) + b = |a * (↑x + ↑y) + b| by exact Eq.symm (abs_of_nonneg (by positivity))] at h4
        linarith
      -- By triangle inequality, |f(x) - f(y)| ≤ |f(x)| + |f(y)| ≤ 50 + 50 = 100
      have h6 : |a * ↑x ^ 2 + b * ↑x + c - (a * ↑y ^ 2 + b * ↑y + c)| ≤ |a * ↑x ^ 2 + b * ↑x + c| + |a * ↑y ^ 2 + b * ↑y + c|:= by exact abs_sub (a * ↑x ^ 2 + b * ↑x + c) (a * ↑y ^ 2 + b * ↑y + c)
      linarith
    .
      -- Case 2: y < -b/2a (y is to the left of the vertex)
      simp at hz
      replace hz : y ≤ -b / (2 * a):= by linarith
      have h4 : a * (y + z) + b < -100:= by
        replace hy : y + z ≤ 2 * y - 1:= by omega
        replace hy : a * (2 * y - 1) ≥ a * (y + z):= by
          have g7 : a ≥ 0:= by linarith
          rify at hy
          exact mul_le_mul_of_nonneg_left hy g7
        replace hz : 2 * a * y ≤ (2 * a) * (-b / (2 * a)):= by
          have g8 : 2 * a ≥ 0:= by linarith
          exact mul_le_mul_of_nonneg_left hz g8
        rw [show 2 * a * (-b / (2 * a)) = -b by field_simp ; linarith] at hz
        linarith
      -- Show that the difference between f(y) and f(z) is greater than 100
      have h5 : |a * ↑y ^ 2 + b * ↑y + c - (a * ↑z ^ 2 + b * ↑z + c)| > 100:= by
        rw [show a * ↑y ^ 2 + b * ↑y + c - (a * ↑z ^ 2 + b * ↑z + c) = (a * (y + z) + b) * (y - z) by ring]
        rw [show |(a * (y + z) + b) * (y - z)| = |a * (y + z) + b| * |(↑y : ℝ) - ↑z| by exact abs_mul (a * (↑y + ↑z) + b) (↑y - ↑z)]
        have g9 : |y - z| ≥ 1:= by
          by_contra H
          simp at H
          linarith
        rify at g9
        replace g9 : |a * (↑y + ↑z) + b| * |(↑y : ℝ) - ↑z| ≥ |a * (↑y + ↑z) + b| * 1:= by
          have g10 : |a * (↑y + ↑z) + b| ≥ 0:= by positivity
          exact mul_le_mul_of_nonneg_left g9 g10
        have g10 : |a * (↑y + ↑z) + b| = -(a * (↑y + ↑z) + b):= by exact abs_of_nonpos (by linarith)
        linarith
      -- By triangle inequality, |f(y) - f(z)| ≤ |f(y)| + |f(z)| ≤ 50 + 50 = 100
      have h6 : |a * ↑y ^ 2 + b * ↑y + c - (a * ↑z ^ 2 + b * ↑z + c)| ≤ |a * ↑y ^ 2 + b * ↑y + c| + |a * ↑z ^ 2 + b * ↑z + c|:= by exact abs_sub (a * ↑y ^ 2 + b * ↑y + c) (a * ↑z ^ 2 + b * ↑z + c)
      linarith
  -- Apply the lemma to each possible ordering of x, y, z to derive a contradiction
  rcases g with g | g | g | g | g | g
  all_goals
    rcases g with ⟨g4, g5⟩
  .
    exact h4 z y x (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  .
    exact h4 y z x (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  .
    exact h4 z x y (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  .
    exact h4 x z y (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  .
    exact h4 y x z (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  .
    exact h4 x y z (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
