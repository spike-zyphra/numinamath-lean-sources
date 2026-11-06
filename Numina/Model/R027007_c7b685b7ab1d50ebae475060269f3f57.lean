import Mathlib

theorem number_theory_12991 {f : ℕ → ℕ} (h : ∀ n, f (n + 2) = f n + 2 ^ n) (hf0 : f 0 = 1) :
    f 2018 % 10 = 2 := by
  have h1 : ∀ (k : ℕ), f (2 * k) = f 0 + ∑ i in Finset.range k, 2 ^ (2 * i : ℕ) := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have eq2 : f (2 * (k + 1 : ℕ)) = f (2 * k + 2 : ℕ) := by
        ring_nf
      rw [eq2]
      rw [h (2 * k)]
      rw [ih]
      simp [Finset.sum_range_succ]
      all_goals
        ring
  have h2 : f 2018 = f 0 + ∑ i in Finset.range 1009, 2 ^ (2 * i : ℕ) := by
    have h3 : f (2 * 1009 : ℕ) = f 0 + ∑ i in Finset.range 1009, 2 ^ (2 * i : ℕ) := by
      apply h1
    have h4 : 2018 = 2 * 1009 := by
      omega
    rw [h4] at *
    all_goals
      linarith [h3]
  rw [h2, hf0]
  native_decide