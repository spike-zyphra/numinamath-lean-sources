import Mathlib

theorem algebra_243937 (m n t : ℕ) (h₀ : m ≠ n) (h₁ : m ≠ t) (h₂ : n ≠ t)
    (h₃ : m + n + m * n = 14) (h₄ : m + t + m * t = 11) (h₅ : n + t + n * t = 19) :
    m = 2 ∧ n = 4 ∧ t = 3 := by
  have h6 : m ≤ 5 := by
    by_contra h
    push_neg at h
    have h7 : n ≤ 1 := by
        nlinarith
    have h8 : n = 0 ∨ n = 1 := by
        omega
    cases' h8 with hn1 hn2
    · -- n = 0
      rw [hn1] at h₃
      have h9 : m = 14 := by nlinarith
      rw [h9] at h₄
      omega
    · -- n = 1
      rw [hn2] at h₃
      omega
  have h7 : n ≤ 5 := by
    by_contra h
    push_neg at h
    have h8 : m ≤ 1 := by
      nlinarith
    have h9 : m = 0 ∨ m = 1 := by
        omega
    cases' h9 with hm1 hm2
    · -- m = 0
      rw [hm1] at h₃
      have h10 : n = 14 := by linarith
      rw [h10] at h₅
      have ht : t = 11 := by
          rw [hm1] at h₄
          linarith
      rw [ht] at h₅
      omega
    · -- m = 1
      rw [hm2] at h₃
      omega
  interval_cases m <;> interval_cases n <;> try { omega }
  <;> omega