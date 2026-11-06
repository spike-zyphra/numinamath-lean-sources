import Mathlib

theorem algebra_288988 {a : ℕ → ℝ} (ha1 : a 1 = -1)
    (han : ∀ n > 0, a n + a (n + 1) + 4 * n + 2 = 0) :
    ∑ i in Finset.range n, a (2 * i + 1) = -2 * n ^ 2 + n := by
  have h1 : ∀ k : ℕ, a (2 * k + 1) = 1 - 2 * (2 * k + 1 : ℕ) := by
    intro k
    induction k with
    | zero =>
      norm_num
      <;> norm_num [ha1]
    | succ k ih =>
      have eq1 := han (2 * k + 1) (by omega)
      have eq2 := han (2 * k + 2) (by omega)
      simp [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at eq1
      simp [show 2 * k + 2 + 1 = 2 * k + 3 by omega] at eq2
      have eq3 : a (2 * k + 2) = -a (2 * k + 1 : ℕ) - 8 * k - 6 := by
        linarith
      have eq4 : a (2 * (k + 1) + 1 : ℕ) = a (2 * k + 1 : ℕ) - 4 := by
        rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega]
        linarith [eq2, eq3]
      have eq5 : a (2 * k + 1 : ℕ) = 1 - 2 * (2 * k + 1 : ℕ) := by
        simpa using ih
      rw [eq5] at eq4
      have eq6 : a (2 * (k + 1) + 1 : ℕ) = 1 - 2 * (2 * (k + 1) + 1 : ℕ) := by
        norm_num at eq4 ⊢
        linarith
      simpa using eq6
  have h2 : ∀ n : ℕ, ∑ i in Finset.range n, a (2 * i + 1) = -2 * (n : ℝ) ^ 2 + (n : ℝ) := by
    intro n
    induction n with
    | zero =>
      simp
      <;> norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have eq1 : a (2 * (n) + 1) = 1 - 2 * (2 * (n : ℕ) + 1 : ℕ) := h1 (n)
      simp [eq1]
      ring_nf
      <;> norm_num
      <;> ring_nf <;> norm_num
  specialize h2 n
  simpa using h2