import Mathlib

theorem algebra_231888 (n : ℕ) (h : n ≠ 0) :
    97 + n * (19 + 91 / n) = 321 ↔ n = 7 := by
  constructor
  · -- Assume the equation holds, prove n = 7
    intro h_eq
    have h1 : n * (19 + 91 / n) = 224 := by
      omega
    have h2 : n ≤ 91 := by
      by_contra h3
      push_neg at h3
      have h3' : 91 / n = 0 := by
        rw [Nat.div_eq_zero_iff]
        omega
      simp [h3'] at h1
      have h4 : n * 19 = 224 := by
        omega
      omega
    interval_cases n <;> norm_num at h1 <;> omega
  · -- Assume n = 7, prove the equation
    intro h_eq
    subst h_eq
    all_goals norm_num