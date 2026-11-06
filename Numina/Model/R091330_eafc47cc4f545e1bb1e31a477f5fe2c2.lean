import Mathlib

theorem number_theory_55496 :
    IsLeast {k : ℕ | ∃ a n : ℕ, a > 0 ∧ n > 1 ∧ k * (3^3 + 4^3 + 5^3) = a^n} 1 := by
  constructor
  · -- Show that 1 is indeed in the set
    use 6, 3
    all_goals norm_num
  · -- Now prove that 1 is the smallest
    intro k hk
    rcases hk with ⟨a, n, ha, hn, h⟩
    have h1 : k > 0 := by
      by_contra h2
      push_neg at h2
      have h3 : k = 0 := by omega
      rw [h3] at h
      have h4 : a ^ n > 0 := by positivity
      have h5 : a ^ n = 0 := by linarith
      linarith
    linarith