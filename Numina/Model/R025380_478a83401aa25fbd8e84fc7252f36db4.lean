import Mathlib

theorem number_theory_322687 (n : ℕ) (h : ∃ k, n = k^2 ∧ ∀ i ∈ Finset.range 35, ⌊Real.sqrt (n + i)⌋ = 17) :
    n = 17^2 := by
  rcases h with ⟨k, hn, hk⟩
  have h0 := hk 0 (by norm_num)
  have eq1 : ⌊Real.sqrt (n : ℝ)⌋ = 17 := by
    norm_num at h0 ⊢
    all_goals try nlinarith
  have h1 : (n : ℝ) = (k : ℝ) ^ 2 := by
    have hn' : n = k^2 := hn
    exact_mod_cast hn'
  have h2 : Real.sqrt ((n : ℝ)) = (k : ℝ) := by
    rw [h1]
    rw [Real.sqrt_sq]
    linarith [show (0 : ℝ) ≤ (k : ℝ) by exact_mod_cast show (0 : ℕ) ≤ k by omega]
  have h3 : ⌊Real.sqrt ((n : ℝ))⌋ = k := by
    rw [h2]
    simp
  have h4 : k = 17 := by 
    nlinarith [h3, eq1]
  have hn1 : n = 17^2 := by
    nlinarith [hn, h4]
  exact hn1