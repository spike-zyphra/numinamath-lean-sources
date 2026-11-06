import Mathlib

theorem number_theory_133319 (n : ℕ) (hn : 1 < n) :
    ¬(2 * n ∣ 3 * n + 1) := by 
  intro h
  rcases h with ⟨k, hk⟩
  have h2 : k < 2 := by
    by_contra h
    push_neg at h
    have hk' : k ≥ 2 := by omega
    have : 2 * n * k ≥ 4 * n := by
      nlinarith [hk']
    have : 3 * n + 1 ≥ 4 * n := by
      nlinarith [hk]
    omega
  have hk0 : k = 0 ∨ k = 1 := by 
    omega
  rcases hk0 with (h | h)
  · -- Assume k = 0
    rw [h] at hk
    nlinarith
  · -- Assume k = 1
    rw [h] at hk
    omega