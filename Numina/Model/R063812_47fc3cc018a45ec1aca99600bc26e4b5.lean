import Mathlib

theorem algebra_158786 (a b c d x y : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9)
    (h₂ : 1 ≤ c ∧ c ≤ 9) (h₃ : 0 ≤ d ∧ d ≤ 9) (h₄ : x = 10 * a + b) (h₅ : y = 10 * c + d)
    (h₆ : ∑ i ∈ Finset.range 40, (i * d + 10 * a + b) = 1000 * a + 100 * b + 10 * c + d) :
    y = 1980 := by
  norm_num [Finset.sum_range_succ] at h₆
  rcases h₀ with ⟨ha1, ha2⟩
  rcases h₁ with ⟨hb1, hb2⟩
  rcases h₂ with ⟨hc1, hc2⟩
  rcases h₃ with ⟨hd1, hd2⟩
  omega