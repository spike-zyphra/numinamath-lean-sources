import Mathlib

theorem number_theory_234898 (n m : ℕ) (h : 2 * m = n ^ 2 + 1) :
    ∃ a b, a ^ 2 + b ^ 2 = m := by
  have h1 : n % 2 = 1 := by
    by_contra h2
    push_neg at h2
    have h2' : n % 2 = 0 := by omega
    have h3 : (n ^ 2) % 2 = 0 := by
      simp [Nat.pow_mod, h2']
    have h4 : (2 * m) % 2 = 1 := by
      omega
    omega

  have h2 : ∃ k, n = 2 * k + 1 := by
    refine ⟨(n - 1) / 2, by omega⟩

  rcases h2 with ⟨k, hk⟩

  have h4 : m = 2 * k^2 + 2 * k + 1 := by
    nlinarith [h, hk]

  use k
  use k + 1

  nlinarith [h4]