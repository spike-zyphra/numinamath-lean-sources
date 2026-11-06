import Mathlib

theorem algebra_314309 {a b : ℕ → ℕ} (ha : ∀ n, a n ≤ a (n + 1)) (hb : ∀ n, b n ≤ b (n + 1))
    (h1 : a 0 ≠ b 0) (h2 : ∀ n, a (n + 2) = a n + a (n + 1)) (h3 : ∀ n, b (n + 2) = b n + b (n + 1))
    (h4 : a 6 = N) (h5 : b 6 = N) :
    N ≥ 104 := by
  have ha2 : a 2 = a 0 + a 1 := by
    apply h2 0

  have ha3 : a 3 = a 1 + a 2 := by
    apply h2 1

  have ha4 : a 4 = a 2 + a 3 := by
    apply h2 2

  have ha5 : a 5 = a 3 + a 4 := by
    apply h2 3

  have ha6 : a 6 = a 4 + a 5 := by
    apply h2 4

  have hb2 : b 2 = b 0 + b 1 := by
    apply h3 0

  have hb3 : b 3 = b 1 + b 2 := by
    apply h3 1

  have hb4 : b 4 = b 2 + b 3 := by
    apply h3 2

  have hb5 : b 5 = b 3 + b 4 := by
    apply h3 3

  have hb6 : b 6 = b 4 + b 5 := by
    apply h3 4
  -- Express a6 and b6 in terms of a0, a1, b0, b1
  have eq_a6 : a 6 = 5 * a 0 + 8 * a 1 := by
    linarith [ha2, ha3, ha4, ha5, ha6]

  have eq_b6 : b 6 = 5 * b 0 + 8 * b 1 := by
    linarith [hb2, hb3, hb4, hb5, hb6]

  rw [h4] at eq_a6
  rw [h5] at eq_b6

  -- Set up inequalities based on non-decreasing property for a and b
  have h6 : 5 * a 0 + 8 * a 1 = 5 * b 0 + 8 * b 1 := by
    linarith [eq_a6, eq_b6]

  have h7 : a 0 ≤ a 1 := by
    apply ha 0

  have h8 : b 0 ≤ b 1 := by
    apply hb 0

  have h9 : a 1 ≤ a 2 := by
    apply ha 1

  have h10 : b 1 ≤ b 2 := by
    apply hb 1

  have h11 : a 2 ≤ a 3 := by
    apply ha 2

  have h12 : b 2 ≤ b 3 := by
    apply hb 2

  -- Simplify inequalities with our expressions
  simp only [ha2] at h9
  simp only [hb2] at h10
  simp only [ha3] at h11
  simp only [hb3] at h12

  have h13 : a 3 ≤ a 4 := by
    apply ha 3

  have h14 : b 3 ≤ b 4 := by
    apply hb 3

  simp only [ha4, ha3] at h13
  simp only [hb4, hb3] at h14

  have h15 : a 4 ≤ a 5 := by
    apply ha 4

  have h16 : b 4 ≤ b 5 := by
    apply hb 4

  simp only [ha5, ha4] at h15
  simp only [hb5, hb4] at h16

  have h17 : a 5 ≤ a 6 := by
    apply ha 5

  have h18 : b 5 ≤ b 6 := by
    apply hb 5

  simp only [ha6, ha5] at h17
  simp only [hb6, hb5] at h18

  -- Combine all equations and inequalities and solve using omega
  omega