import Mathlib

theorem number_theory_136441 (a : ℕ → ℕ) (h : ∀ n, a n > 0)
    (h' : ∀ n ≤ 1968, {x | a x ∣ n}.encard = n) :
    ∃ m, a m = 1024 := by 
  have h0 := h' 0 (by norm_num)
  have h1 : {x | a x ∣ 0} = Set.univ := by
    ext m
    simp [Nat.dvd_zero]
  rw [h1] at h0
  simp at h0
  all_goals linarith