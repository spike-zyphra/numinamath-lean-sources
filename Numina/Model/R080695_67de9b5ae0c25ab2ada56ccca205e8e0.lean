import Mathlib

theorem number_theory_216844 (p k : ℕ) (hp : Nat.Prime p) (hk : Nat.Prime (2 * p + 1))
    (hpk : k < 2 * p + 1) :
    ∃ n, n > 0 ∧ (2 * p + 1 - n) = k ∨ n = k := by
  by_cases hk' : k > 0
  · use k
    right
    rfl
  · -- k = 0
    have hk0 : k = 0 := by linarith
    use 2 * p + 1
    left
    constructor
    · -- Show that 2p + 1 > 0
      have hp_pos : p > 0 := by
        by_contra h
        push_neg at h
        have : p = 0 := by linarith
        rw [this] at hp
        norm_num at hp
      linarith
    · -- Show that 2 * p + 1 - (2 * p + 1) = k
      simp [hk0]