import Mathlib

theorem algebra_175585 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n) (ha0 : a 0 = 25) (hb0 : b 0 = 75)
    (han : a 99 + b 99 = 100) :
    ∑ i in Finset.range 100, (a i + b i) = 10000 := by
  rcases ha with ⟨d₁, had₁⟩
  rcases hb with ⟨d₂, had₂⟩
  have a99 : a 99 = a 0 + d₁ * 99 := by
    rw [had₁ 99]
    ring
  have b99 : b 99 = b 0 + d₂ * 99 := by
    rw [had₂ 99]
    ring
  rw [a99, b99, ha0, hb0] at han
  have h1 : d₁ + d₂ = 0 := by linarith
  have seq_sum_eq : ∑ i in Finset.range 100, (a i + b i) = 10000 := by
    simp [Finset.sum_range_succ, ha0, hb0, had₁, had₂]
    linarith
  exact seq_sum_eq