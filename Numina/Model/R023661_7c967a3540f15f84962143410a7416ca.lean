import Mathlib

theorem algebra_129137 {x : ℝ} (a : ℕ → ℝ)
    (h₀ : ∀ n, a n = 1 + x ^ (n + 1) + x ^ (n + 2))
    (h₁ : a 2 ^ 2 = a 1 * a 3) :
    ∀ n ≥ 3, a n ^ 2 = a (n - 1) * a (n + 1) := by
  have ha1 : a 1 = 1 + x^2 + x^3 := by
    rw [h₀ 1]
    <;> ring_nf
  have ha2 : a 2 = 1 + x^3 + x^4 := by
    rw [h₀ 2]
    <;> ring_nf
  have ha3 : a 3 = 1 + x^4 + x^5 := by
    rw [h₀ 3]
    <;> ring_nf
  rw [ha2, ha1, ha3] at h₁
  have hx2 : x^2 * (x - 1)^2 * (x + 1) = 0 := by
    nlinarith [sq_nonneg (x^2), sq_nonneg (x^2 - 1), sq_nonneg (x + 1), sq_nonneg (x - 1)]
  have hx_eq : x = 0 ∨ x = 1 ∨ x = -1 := by
    cases (mul_eq_zero.mp hx2) with
    | inl h1 =>
      cases (mul_eq_zero.mp h1) with
      | inl h2 => 
        have h_eq : x^2 = 0 := by linarith
        have : x = 0 := by
          nlinarith
        simp [this]
      | inr h3 => 
        have h_eq : (x - 1)^2 = 0 := by linarith
        have : x - 1 = 0 := by
          apply pow_eq_zero 
          exact h_eq
        have hx1 : x = 1 := by linarith
        simp [hx1]
    | inr h4 =>
      have h_eq : x + 1 = 0 := by linarith
      have hx1 : x = -1 := by linarith
      simp [hx1]
  intro n hn
  rcases hx_eq with h_eq | h_eq | h_eq
  · -- Case x = 0
    have h2 : ∀ n, a n = (1 : ℝ) := by
      intro n
      rw [h₀ n]
      rw [h_eq]
      norm_num
    rw [h2 n, h2 (n - 1), h2 (n + 1)]
    all_goals norm_num
    all_goals nlinarith
  · -- Case x = 1
    have h2 : ∀ n, a n = (1 + (1 : ℝ) ^ (n + 1) + (1 : ℝ) ^ (n + 2) ) := by
      intro n
      rw [h₀ n]
      rw [h_eq]
      all_goals norm_num
    rw [h2 n, h2 (n - 1), h2 (n + 1)]
    have h3 : (1 : ℝ) ^ (n + 1) = 1 := by
      have h1_pow : ∀ k : ℕ, (1 : ℝ) ^ k = 1 := by
        intro k
        exact by simp
      specialize h1_pow (n + 1)
      simpa using h1_pow
    have h4 : (1 : ℝ) ^ (n + 2) = 1 := by
      have h1_pow : ∀ k : ℕ, (1 : ℝ) ^ k = 1 := by
        intro k
        exact by simp
      specialize h1_pow (n + 2)
      simpa using h1_pow
    have h5 : (1 : ℝ) ^ ((n - 1 : ℕ) + 1) = 1 := by
      have h1_pow : ∀ k : ℕ, (1 : ℝ) ^ k = 1 := by
        intro k
        exact by simp
      specialize h1_pow ((n - 1 : ℕ) + 1)
      simpa using h1_pow
    have h6 : (1 : ℝ) ^ ((n - 1 : ℕ) + 2) = 1 := by
      have h1_pow : ∀ k : ℕ, (1 : ℝ) ^ k = 1 := by
        intro k
        exact by simp
      specialize h1_pow ((n - 1 : ℕ) + 2)
      simpa using h1_pow
    have h7 : (1 : ℝ) ^ ((n + 1 : ℕ) + 1) = 1 := by
      have h1_pow : ∀ k : ℕ, (1 : ℝ) ^ k = 1 := by
        intro k
        exact by simp
      specialize h1_pow ((n + 1 : ℕ) + 1)
      simpa using h1_pow
    have h8 : (1 : ℝ) ^ ((n + 1 : ℕ) + 2) = 1 := by
      have h1_pow : ∀ k : ℕ, (1 : ℝ) ^ k = 1 := by
        intro k
        exact by simp
      specialize h1_pow ((n + 1 : ℕ) + 2)
      simpa using h1_pow
    simp only [h3, h4, h5, h6, h7, h8] at *
    all_goals norm_num
    all_goals nlinarith
  · -- Case x = -1
    have h2 : ∀ n, a n = 1 + (-1 : ℝ) ^ (n + 1) + (-1 : ℝ) ^ (n + 2) := by
      intro n
      rw [h₀ n]
      rw [h_eq]
      all_goals norm_num
    rw [h2 n, h2 (n - 1), h2 (n + 1)]
    have h3 : n ≥ 3 := by linarith
    ring_nf
    <;> norm_num [pow_add, pow_mul]
    <;> norm_num
    <;> ring
    <;> omega