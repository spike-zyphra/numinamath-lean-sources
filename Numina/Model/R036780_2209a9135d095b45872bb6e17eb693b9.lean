import Mathlib

theorem algebra_152572 {a b : ℝ} (x : ℕ → ℝ) (hx : ∀ n, x (n + 2) = x (n + 1) - x n)
    (hx1 : x 0 = a) (hx2 : x 1 = b) :
    x 99 = -a ∧ ∑ i in Finset.range 100, x i = 2 * b - a := by
  have h1 : ∀ n, x (n + 6) = x n := by
    intro n
    have h1 := hx n
    have h2 := hx (n + 1)
    have h3 := hx (n + 2)
    have h4 := hx (n + 3)
    have h5 := hx (n + 4)
    have h6 := hx (n + 5)
    simp [show n + 2 + 1 = n + 3 by omega, show n + 2 + 2 = n + 4 by omega,
      show n + 3 + 1 = n + 4 by omega, show n + 3 + 2 = n + 5 by omega,
      show n + 4 + 1 = n + 5 by omega, show n + 4 + 2 = n + 6 by omega,
      show n + 5 + 1 = n + 6 by omega] at h1 h2 h3 h4 h5 h6
    linarith [h1, h2, h3, h4, h5, h6]
  -- Now, to compute x_{99}:
  -- 99 = 6 * 16 + 3, so 99 ≡ 3 (mod 6)
  -- So x_{99} should be equal to x_3
  -- Let's compute x_3
  -- x_0 = a
  -- x_1 = b
  -- x_2 = x_1 - x_0 = b - a
  -- x_3 = x_2 - x_1 = (b - a) - b = -a
  -- So x_{99} = -a
  have hx99 : x 99 = -a := by
    have h2 : ∀ n, x (n + 6) = x n := by
      intro n
      have h1 := hx n
      have h2 := hx (n + 1)
      have h3 := hx (n + 2)
      have h4 := hx (n + 3)
      have h5 := hx (n + 4)
      have h6 := hx (n + 5)
      simp [show n + 2 + 1 = n + 3 by omega, show n + 2 + 2 = n + 4 by omega,
        show n + 3 + 1 = n + 4 by omega, show n + 3 + 2 = n + 5 by omega,
        show n + 4 + 1 = n + 5 by omega, show n + 4 + 2 = n + 6 by omega,
        show n + 5 + 1 = n + 6 by omega] at h1 h2 h3 h4 h5 h6
      linarith [h1, h2, h3, h4, h5, h6]
    -- Now, to compute x_{99}
    -- 99 = 6 * 16 + 3
    -- So x_{99} = x_{3}
    -- Let's compute x_3
    -- x_0 = a
    -- x_1 = b
    -- x_2 = x_1 - x_0 = b - a
    -- x_3 = x_2 - x_1 = (b - a) - b = -a
    -- So x_{99} = -a
    have h3 : ∀ k : ℕ, x (3 + 6 * k) = -a := by
      intro k
      induction k with
      | zero =>
        -- Base case k = 0
        -- x(3) = -a
        norm_num [hx1, hx2, hx] at *
        <;> linarith
      | succ k ih =>
        calc
          x (3 + 6 * (k + 1)) = x (3 + 6 * k + 6) := by ring_nf
          _ = x (3 + 6 * k) := by rw [h2]
          _ = -a := by exact ih
    have h4 : 99 = 3 + 6 * 16 := by norm_num
    rw [h4]
    exact h3 16
  -- Now for the sum
  have hsum : ∑ i in Finset.range 100, x i = 2 * b - a := by
    simp [Finset.sum_range_succ, hx1, hx2, hx]
    <;> norm_num [hx1, hx2, hx] at *
    <;> linarith
  constructor
  · exact hx99
  · exact hsum