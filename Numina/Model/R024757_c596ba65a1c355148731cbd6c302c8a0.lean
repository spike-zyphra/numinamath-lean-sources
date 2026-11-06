import Mathlib

theorem number_theory_170326 (n : ℕ) (h₀ : Even n) (h₁ : Nat.digits 2 n = [0, n]) :
    Nat.digits 3 n = [0, n] ↔ n = 10 ∨ n = 12 := by
  exfalso
  have h2 : n ≤ 1 := by
    by_contra h
    push_neg at h
    have h4 : n ≥ 2 := by linarith
    have h5 : Nat.digits 2 n ≠ [0, n] := by
      have h6 : n ≥ 2 := h4
      intro h
      have h11 : n < 2 := by
        have h11 : n ∈ Nat.digits 2 n := by
          simp [h] at *
          all_goals
            omega
        exact Nat.digits_lt_base (by norm_num) h11
      omega
    contradiction
  have h6 : n = 0 := by
    have h7 : n ≤ 1 := h2
    have h7 : n = 0 ∨ n = 1 := by
      omega
    rcases h7 with (r | r)
    · tauto
    · -- n = 1
      have h8 : ¬Even (1 : ℕ) := by decide
      rw [r] at h₀
      contradiction
  rw [h6] at h₁
  norm_num at h₁
  all_goals try { contradiction }
  all_goals try { tauto }