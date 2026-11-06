import Mathlib

theorem number_theory_1727 (x y : ℕ) (hx : x < 10) (hy : y < 10) (h : IsSquare (Nat.ofDigits 10 [1, y, 9, x, 2])) :
    3 * x + 7 * y = 29 := by
  have h1 : Nat.ofDigits 10 [1, y, 9, x, 2] = 20000 + 1000 * x + 900 + 10 * y + 1 := by 
    simp [Nat.ofDigits, mul_add, mul_comm]
    <;> ring
  rw [h1] at h 
  rcases h with ⟨k, hk⟩
  have h2 : k ≤ 173 := by
    by_contra h
    push_neg at h
    have h3 : k ^ 2 > 29991 := by
      nlinarith
    nlinarith
  have h3 : k ≥ 145 := by 
    by_contra h 
    push_neg at h 
    have h4 : k ^ 2 < 20901 := by
      nlinarith
    nlinarith
  interval_cases k <;> norm_num at hk <;> 
    omega