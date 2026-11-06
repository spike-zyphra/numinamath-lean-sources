import Mathlib

theorem algebra_623484 (d : ℝ) (a S : ℕ → ℝ) (ha : ∀ n : ℕ, a n = a 0 + n * d) (hS : ∀ n : ℕ, S n = ∑ i in Finset.range n, a i) (h1 : S 10 = 0) (h2 : S 15 = 25) : IsLeast {b : ℝ | ∃ n : ℕ, n ≥ 1 ∧ b = n * S n} (-49):= by
  have h : ∀ n : ℕ, S (n + 1) = (n + 1) * a 0 + n * (n + 1) * d / 2:= by
    intro n
    induction n with
    | zero =>
      simp [hS]
    | succ n ih =>
      rw [hS (n + 1 + 1), Finset.sum_range_succ, ←hS (n + 1), ih, ha (n + 1)]
      simp
      linarith
  rw [h 9] at h1
  rw [h 14] at h2
  simp at h1 h2
  replace h1 : d = 2 / 3:= by linarith
  replace h2 : a 0 = -3:= by linarith
  rw [h1, h2] at h
  replace h : ∀ n : ℕ, n ≥ 1 → S n = 1 / 3 * n ^ 2 - 10 / 3 * n:= by
    intro n hn
    set m:= n - 1 with hm
    clear_value m
    replace hm : n = m + 1:= by omega
    subst n
    rw [h m]
    simp at *
    linarith
  constructor
  · -- Show that -49 is in the set.
    use 7
    constructor
    · norm_num
    · -- Show that 7 * S 7 = -49.
      rw [h 7 (by omega)]
      norm_num
  · -- Show that -49 is the least element in the set.
    intro x hx
    rcases hx with ⟨n, hn, hxn⟩
    by_cases h' : n ≤ 7
    · -- Case where n ≤ 7
      have hn1 : n ≤ 7 := h'
      have hn2 : n ≥ 1 := by omega
      interval_cases n <;> norm_num [h] at hxn ⊢ <;> nlinarith
    · -- Case where n > 7
      have hn1 : n ≥ 8 := by omega
      have hn1' : (n : ℝ) ≥ (8 : ℝ) := by exact_mod_cast hn1
      have hn2 : n ≥ 1 := by omega
      rw [h n (by omega)] at hxn
      nlinarith [sq_nonneg ((n : ℝ) - (7 : ℝ)), sq_nonneg ((n : ℝ) - (20 / 3 : ℝ)), sq_nonneg ((n : ℝ) - (20 / 3 : ℝ)), sq_nonneg ((n : ℝ) - (20 / 3 : ℝ)), sq_nonneg ((n : ℝ) - (8 : ℝ)), sq_nonneg ((n : ℝ) - (8 : ℝ))]