import Mathlib

theorem algebra_11801 {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ha1 : a 1 = 2012) (ha2 : ∃ m n, a 2 = m ∧ a 3 = n)
    (ha3 : ∃ r, ∀ n ≥ 1, r ≤ 10 ∧ ∀ n ≥ 1, n * a n - n ^ 2 = r ^ n) :
    ∀ n ≥ 1, a n = (2011 * 6 ^ (n - 1)) / n + n := by
  rcases ha3 with ⟨r, hr⟩
  have h1 := (hr 1 (by norm_num)).2 1 (by norm_num)
  rw [ha1] at h1
  norm_num at h1 
  have hr1 := (hr 1 (by norm_num)).1
  linarith