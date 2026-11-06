import Mathlib

theorem number_theory_274749 (n : ℕ) (h₀ : n > 1) (h₁ : Nat.digits n 136 = [3, 5, 2]) :
    n = 7 := by
  have h2 : n ≤ 136 := by
    by_contra h
    push_neg at h
    have h3 : Nat.digits n 136 = [136] := by
      simp [h]
    rw [h3] at h₁
    norm_num at h₁
  interval_cases n <;> norm_num at h₁ ⊢
  all_goals omega