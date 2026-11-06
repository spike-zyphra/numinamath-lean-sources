import Mathlib

theorem algebra_326246 {f : ℕ → ℕ} (h : ∀ m n, 0 < m → 0 < n → f (m + n) = f m + f n + m * n)
    (h3 : f 3 = 6) : f 2011 = 2023066 := by
  have eq1 : f 3 = f 1 + f 2 + 1 * 2 := h 1 2 (by norm_num) (by norm_num)
  rw [h3] at eq1
  have eq2 : f 2 = f 1 + f 1 + 1 * 1 := h 1 1 (by norm_num) (by norm_num)
  have h1 : f 1 = 1 := by
    omega
  have h2 : f 2 = 3 := by
    omega
  have h4 : ∀ n : ℕ, f (n + 1) = (n + 1) * (n + 2) / 2 := by
    intro n
    induction n with
    | zero =>
      norm_num [h1]
    | succ n ih =>
      have eq1 := h (n + 1) 1 (by omega) (by norm_num)
      simp [ih, h1] at eq1 ⊢
      ring_nf at eq1 ⊢
      <;> omega
  have h5 : f 2011 = 2011 * 2012 / 2 := by
    specialize h4 2010
    norm_num at h4 ⊢
    <;> omega
  norm_num [h5]