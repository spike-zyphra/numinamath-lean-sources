import Mathlib

open Real Set
open scoped Real

theorem algebra_303222 {θ : ℝ} (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (n : ℕ) (hn : 0 < n) (h : sin θ ^ 4 / a + cos θ ^ 4 / b = 1 / (a + b)) :
  sin θ ^ (2 * n) / a ^ (n - 1) + cos θ ^ (2 * n) / b ^ (n - 1) =
  1 / (a + b) ^ (n - 1) := by

  have ha1 : 0 < a * b := mul_pos ha hb
  have h1 : sin θ ^ 4 * (b * (a + b)) + cos θ ^ 4 * (a * (a + b)) = a * b := by
    have h1 : sin θ ^ 4 / a + cos θ ^ 4 / b = 1 / (a + b) := h
    have ha' : a ≠ 0 := by linarith
    have hb' : b ≠ 0 := by linarith
    have hab : a + b ≠ 0 := by linarith
    field_simp [ha', hb', hab] at h1 ⊢
    nlinarith

  have h2 : sin θ ^ 2 + cos θ ^ 2 = 1 := by exact Real.sin_sq_add_cos_sq θ

  have h3 : sin θ ^ 2 = a / (a + b) := by
    have h4 : sin θ ^ 4 * (b * (a + b)) + cos θ ^ 4 * (a * (a + b)) = a * b := h1
    have h5 : sin θ ^ 4 = (sin θ ^ 2) ^ 2 := by ring
    have h6 : cos θ ^ 4 = (cos θ ^ 2) ^ 2 := by ring
    rw [h5, h6] at h4
    have h7 : cos θ ^ 2 = 1 - sin θ ^ 2 := by linarith [h2]
    rw [h7] at h4
    field_simp [(show a + b ≠ 0 by positivity), (show a ≠ 0 by linarith), (show b ≠ 0 by linarith)] at h4 ⊢
    nlinarith [sq_nonneg ( (a + b) * sin θ ^ 2 - a ) ]

  have h4 : cos θ ^ 2 = b / (a + b) := by
    have h3' : sin θ ^ 2 = a / (a + b) := h3
    have h2' : sin θ ^ 2 + cos θ ^ 2 = 1 := h2
    have h9 : cos θ ^ 2 = 1 - sin θ ^ 2 := by linarith
    rw [h9, h3']
    field_simp
    all_goals nlinarith

  have h5 : ∀ (n : ℕ), sin θ ^ (2 * n) = (sin θ ^ 2) ^ n := by
    intro n
    have h7 : sin θ ^ (2 * n) = (sin θ ^ 2) ^ n := by
      rw [← pow_mul]
    exact h7

  have h6 : ∀ (n : ℕ), cos θ ^ (2 * n) = (cos θ ^ 2) ^ n := by
    intro n
    have h7 : cos θ ^ (2 * n) = (cos θ ^ 2) ^ n := by
      rw [← pow_mul]
    exact h7

  have h7 : sin θ ^ (2 * n) = (a / (a + b)) ^ n := by
    rw [h5 n]
    rw [h3]

  have h8 : cos θ ^ (2 * n) = (b / (a + b)) ^ n := by
    rw [h6 n]
    rw [h4]

  rw [h7, h8]

  cases n with
  | zero =>
    exfalso
    linarith
  | succ n =>
    simp at *
    have h17 : (a / (a + b)) ^ (n + 1) / a ^ n + (b / (a + b)) ^ (n + 1) / b ^ n = 1 / (a + b) ^ n := by
      have ha' : a ≠ 0 := by linarith
      have hb' : b ≠ 0 := by linarith
      have ha'' : a + b ≠ 0 := by linarith
      field_simp
      <;> ring
    simpa using h17