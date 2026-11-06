import Mathlib

theorem algebra_98078 (a b : ℕ → ℝ) (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n) (ha0 : a 0 = 25) (hb0 : b 0 = 75)
    (h100 : a 99 + b 99 = 100) :
    ∑ i in Finset.range 100, (a i + b i) = 10000 := by
  rcases ha with ⟨d_a, had⟩
  rcases hb with ⟨d_b, hdb⟩
  have h1 : a 99 = a 0 + d_a * 99 := by
    specialize had 99
    norm_num at had ⊢
    linarith
  have h2 : b 99 = b 0 + d_b * 99 := by
    specialize hdb 99
    norm_num at hdb ⊢
    linarith 
  rw [h1, h2, ha0, hb0] at h100
  have h3 : d_a + d_b = 0 := by
    linarith 
  have h4 : ∀ i : ℕ, a i + b i = 100 := by 
    intro i
    have had_i : a i = a 0 + d_a * i := by
      specialize had i
      simpa using had
    have hdb_i : b i = b 0 + d_b * i := by 
      specialize hdb i
      simpa using hdb 
    rw [had_i, hdb_i, ha0, hb0]
    have h6 : d_b = -d_a := by linarith 
    rw [h6]
    ring
  -- Now compute the sum
  have h6 : ∑ i in Finset.range 100, (a i + b i) = 10000 := by
    have h7 : ∀ i : ℕ, a i + b i = 100 := h4
    simp_rw [h7]
    norm_num [Finset.sum_const, Finset.card_range]
  exact h6