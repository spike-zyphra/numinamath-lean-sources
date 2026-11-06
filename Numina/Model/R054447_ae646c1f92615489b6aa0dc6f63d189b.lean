import Mathlib

theorem algebra_249269 (x y : ℕ → ℝ)
    (hx0 : x 0 = 0) (hy0 : y 0 = 1)
    (hxn : ∀ n, x (n + 1) = (3 * x n + y n) / 4)
    (hy : ∀ n, y (n + 1) = (2 * x n + 3 * y n) / 5) :
    ∃ r, ∀ n, (y n - x n) = r ^ n := by
  use 7 / 20
  intro n
  have hz : ∀ n, y n - x n = (7 / 20) ^ n := by
    intro n
    induction n with
    | zero =>
      rw [hx0, hy0]
      all_goals norm_num
    | succ n ih =>
      have h1 : x (n + 1) = (3 * x n + y n) / 4 := hxn n
      have h2 : y (n + 1) = (2 * x n + 3 * y n) / 5 := hy n
      calc 
        y (n + 1) - x (n + 1) = ((2 * x n + 3 * y n) / 5) - ((3 * x n + y n) / 4) := by 
          rw [h1, h2]
          all_goals ring
        _ = (7 / 20) * (y n - x n) := by 
          ring
        _ = (7 / 20) * ((7 / 20) ^ n) := by 
          rw [ih]
        _ = (7 / 20) ^ (n + 1) := by 
          ring_nf
  specialize hz n
  simpa using hz