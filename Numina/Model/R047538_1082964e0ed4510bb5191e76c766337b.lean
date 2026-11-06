import Mathlib

theorem algebra_213629 {S : ℕ → ℝ} (hS : ∃ a d, ∀ n, S n = a * n + d * (n * (n - 1)) / 2)
    (n k : ℕ) (hn : n > k) (hk : k ≥ 1) :
    (S (n + k)) / (n + k) = (S n - S k) / (n - k) := by
  rcases hS with ⟨a, d, hS⟩
  have eq1 : S (n + k) = a * (n + k) + d * ((n + k) * ((n + k) - 1)) / 2 := by 
    specialize hS (n + k)
    simpa using hS
  have eq2 : S n = a * n + d * (n * (n - 1)) / 2 := by 
    specialize hS n 
    simpa using hS
  have eq3 : S k = a * k + d * (k * (k - 1)) / 2 := by 
    specialize hS k 
    simpa using hS
  have eq4 : (S (n + k)) / (n + k) = a + d * ((n + k) - 1) / 2 := by
    rw [eq1]
    have : (↑n + ↑k : ℝ) > (0 : ℝ) := by
      have hn1 : (n : ℝ) > (0 : ℝ) := by
        have hn2 : n ≥ 1 := by omega
        have hn3 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast hn2
        nlinarith
      have hk1 : (k : ℝ) > (0 : ℝ) := by
        have hk2 : k ≥ 1 := by omega
        have hk3 : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast hk2
        nlinarith
      nlinarith
    field_simp at *
    ring
  have eq5 : (S n - S k) / (n - k) = a + d * (n * (n - 1) - k * (k - 1)) / (2 * (n - k)) := by
    rw [eq2, eq3]
    have hk1 : k ≥ 1 := by omega 
    have hn2 : n > k := by omega 
    have h1 : (n - k : ℕ) > (0 : ℕ) := by 
      omega 
    have h2 : (n : ℝ) > (k : ℝ) := by 
      exact_mod_cast show n > k by omega 
    have h3 : (n - k : ℝ) > (0 : ℝ) := by 
      have h1 : (n : ℝ) > (k : ℝ) := by 
        exact_mod_cast show (n : ℕ) > (k : ℕ) by omega 
      nlinarith 
    field_simp at *
    ring_nf
  rw [eq4, eq5]
  have hk1 : k ≥ 1 := by omega 
  have hn2 : n > k := by omega 
  have h1 : (n - k : ℕ) > (0 : ℕ) := by 
    omega 
  have h2 : (n : ℝ) > (k : ℝ) := by 
    exact_mod_cast show n > k by omega 
  have h3 : (n - k : ℝ) > (0 : ℝ) := by 
    have h1 : (n : ℝ) > (k : ℝ) := by 
      exact_mod_cast show (n : ℕ) > (k : ℕ) by omega 
    nlinarith 
  field_simp at *
  ring_nf