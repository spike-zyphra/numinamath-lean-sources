import Mathlib

theorem number_theory_272208 (n : ℕ) (h : Nat.digits n (4 * 13) = [0, 0, 1]) :
    n = 6 := by
  have h1 : n ≤ 52 := by
    by_contra h1
    push_neg at h1
    have h2 : Nat.digits n (4 * 13) = [4 * 13] := by
      simp [h1]
    rw [h2] at h
    norm_num at h
  interval_cases n <;> norm_num at h <;> all_goals trivial