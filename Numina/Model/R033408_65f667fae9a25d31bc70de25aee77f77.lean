import Mathlib

theorem algebra_327648 {n : ℤ} (hn : ∃ x y, x ≠ y ∧ x^2-6*x-4*n^2-32*n=0 ∧ y^2-6*y-4*n^2-32*n=0) :
    n=-18 ∨ n=-8 ∨ n=0 ∨ n=10 := by
  rcases hn with ⟨x, y, hxy, hx, hy⟩
  have h1 : (x : ℤ) + y = 6 := by
    have h2 : (x - y) * (x + y - 6) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Suppose x - y = 0, which contradicts our assumption that x ≠ y.
      exfalso
      apply hxy
      linarith
    · -- So we have x + y - 6 = 0.
      linarith
  have h2 : x * y = -4 * n^2 -32 * n := by
    have h3 : x^2-6*x-4*n^2-32*n=0 := hx
    have h4 : y^2-6*y-4*n^2-32*n=0 := hy
    have h5 : x + y = 6 := h1
    have h6 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by 
      linarith 
    rw [show x + y = 6 by linarith] at h6
    nlinarith [h3, h4, h6]
  have h3 : (x - y) ^ 2 = 16 * n ^ 2 + 128 * n + 36 := by
    have h4 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
      ring
    rw [h4, h1, h2]
    ring
  have h4 : (x - y) ^ 2 = 16 * n ^ 2 + 128 * n + 36 := h3
  have h5' : ∃ k : ℤ, k^2 = (16 * n ^ 2 + 128 * n + 36) := by
    use (x - y)
    all_goals nlinarith
  rcases h5' with ⟨k, hk⟩
  have h7 : (k : ℤ) ^ 2 = 16 * (n + 4) ^ 2 - 220 := by 
    nlinarith
  have h8 : (k - 4 * (n + 4)) * (k + 4 * (n + 4)) = -220 := by
    nlinarith
  have h9 : k - 4 * (n + 4) ∣ -220 := by 
    use k + 4 * (n + 4)
    all_goals nlinarith
  have h10 : k - 4 * (n + 4) ∣ 220 := by
    exact Int.dvd_neg.mp h9
  have h11 : k - 4 * (n + 4) ≤ 220 := by
    apply Int.le_of_dvd (show 0 < (220 : ℤ) by norm_num) h10
  have h12 : k - 4 * (n + 4) ≥ -220 := by 
    have h13 : -(k - 4 * (n + 4)) ∣ 220 := by 
      exact Int.neg_dvd.2 h10
    have h14 : -(k - 4 * (n + 4)) ≤ 220 := by
      apply Int.le_of_dvd (show 0 < (220 : ℤ) by norm_num) h13
    linarith
  interval_cases h : k - 4 * (n + 4) <;> omega