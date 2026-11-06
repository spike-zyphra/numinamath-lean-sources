import Mathlib

theorem inequalities_309062 (A : ℕ → ℝ) (hA : ∀ n, A n = ∑ i in Finset.range n, (i + 1)) :
    ∀ n, 6 ≤ n → A n ≥ (1 / 12) * (n ^ 2 - 4 * n - 5) := by 
  intro n hn
  have h1 : A n = (↑n * (↑n + 1)) / 2 := by
    rw [hA n]
    have h2 : ∀ (n : ℕ), ∑ i in Finset.range n, (i + 1 : ℝ) = (↑n * (↑n + 1)) / 2 := by
      intro n
      induction n with
      | zero =>
        simp
        <;> norm_num
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp
        <;> ring_nf <;> norm_num
        <;> linarith
    specialize h2 n
    simpa using h2
  
  rw [h1]
  have h2 : (↑n : ℝ) ≥ (6 : ℝ) := by
    exact_mod_cast hn
  
  have h3 : (↑n * (↑n + 1) / 2 : ℝ) ≥ (1 / 12) * (↑n ^ 2 - 4 * ↑n - 5) := by
    have h4 : (↑n * (↑n + 1) / 2 : ℝ) - (1 / 12) * (↑n ^ 2 - 4 * ↑n - 5) ≥ 0 := by
      have h5 : (↑n * (↑n + 1) / 2 : ℝ) - (1 / 12) * (↑n ^ 2 - 4 * ↑n - 5) = (5 * (↑n + 1) ^ 2) / 12 := by
        field_simp
        ring_nf
      rw [h5]
      have h6 : (↑n : ℝ) ≥ 0 := by linarith
      have h7 : (↑n + 1 : ℝ) ^ 2 ≥ 0 := by nlinarith
      positivity
    linarith
  
  linarith