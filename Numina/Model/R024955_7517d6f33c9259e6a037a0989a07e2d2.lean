import Mathlib

def x (n : ℕ) : ℤ := match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => 4 * x (n + 1) - x n

def y (n : ℕ) : ℤ := match n with
  | 0 => 1
  | 1 => 2
  | n + 2 => 4 * y (n + 1) - y n

theorem algebra_53255 {n : ℕ} : (y n)^2 = 3 * (x n)^2 + 1 := by
  let rec f : (n : ℕ) → y n ^ 2 = 3 * (x n) ^ 2 + 1 ∧ y (n + 1) * y n = 3 * x (n + 1) * x n + 2
    | 0 => by
      constructor
      · -- Show that $y_0^2 = 3x_0^2 + 1$.
        simp [y, x]
      · -- Show that $y_1 \cdot y_0 = 3x_1 x_0 + 2$.
        simp [y, x]
    | 1 => by
      constructor
      · -- Show that $y_1^2 = 3x_1^2 + 1$.
        simp [y, x]
      · -- Show that $y_2 \cdot y_1 = 3 x_2 x_1 + 2$.
        simp [y, x]
    | n + 2 => by
      have h1 := f (n)
      have h2 := f (n + 1)
      constructor
      · -- Show that $y_{n+2}^2 = 3x_{n+2}^2 + 1$.
        simp [y, x] at h1 h2 ⊢
        nlinarith [h1.1, h1.2, h2.1, h2.2]
      · -- Show that $y_{n+3} \cdot y_{n+2} = 3 x_{n+3} x_{n+2} + 2$.
        simp [y, x] at h1 h2 ⊢
        nlinarith [h1.1, h1.2, h2.1, h2.2]
  exact (f n).1