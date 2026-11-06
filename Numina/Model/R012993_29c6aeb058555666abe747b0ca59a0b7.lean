import Mathlib

theorem algebra_46374 (f : ℤ → ℤ) (hf : ∀ x, f x = x ^ 2 + 3 * x + 2)
    (g : ℤ → ℤ → ℤ) (hg : ∀ b c, g b c = b ^ 2 - b + 3 * c ^ 2 + 3 * c) :
    ∀ a > 0, ∃ b c : ℤ, b > 0 ∧ c > 0 ∧ f a = g b c := by
  intro a ha
  have h1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
  rcases h1 with (h | h)
  · -- a is even
    have h2 : ∃ k : ℤ, a = 2 * k := by
      refine' ⟨a / 2, by omega⟩
    rcases h2 with ⟨k, hk⟩
    use k + 2, k
    constructor
    · -- Show b > 0
      nlinarith [show k ≥ 1 by omega]
    constructor
    · -- Show c > 0
      nlinarith [show k ≥ 1 by omega]
    · -- Show f a = g (k + 2) k
      rw [hf a, hg (k + 2) k]
      nlinarith [show k ≥ 1 by omega, hk]
  · -- a is odd
    have h2 : ∃ k : ℤ, a = 2 * k + 1 := by
      have : a % 2 = 1 := by omega
      refine' ⟨(a - 1) / 2, by omega⟩
    rcases h2 with ⟨k, hk⟩
    use k + 1, k + 1
    constructor
    · -- Show b > 0
      nlinarith [show k ≥ 0 by omega, hk]
    constructor
    · -- Show c > 0
      nlinarith [show k ≥ 0 by omega, hk]
    · -- Show f a = g (k + 1) (k + 1)
      rw [hf a, hg (k + 1) (k + 1)]
      nlinarith [show k ≥ 0 by omega, hk]