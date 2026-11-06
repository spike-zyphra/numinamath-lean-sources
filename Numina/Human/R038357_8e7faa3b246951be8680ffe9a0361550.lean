import Mathlib

def seq : ℕ → ℕ
| 0 => 5
| n + 1 => (seq n) * 10 + 5

/- In the sequence of numbers $5, 55, 555, 5555, \ldots$ Are any of the numbers in this sequence divisible by 495 ; if so, what is the smallest such number? -/
theorem number_theory_237412 :
    IsLeast {x | ∃ n, x = seq n ∧ 495 ∣ x} 555555555555555555 := by
  constructor

  · -- First, show that 555555555555555555 is indeed in the set
    use 17
    norm_num [seq]

  · -- Then, show there is no smaller element in the set
    intro n hn
    rcases hn with ⟨m, hm_eq, hm_div⟩
    by_contra h
    push_neg at h

    have h1 : m < 18 := by
      by_contra h2
      push_neg at h2
      have h3 : seq m ≥ 555555555555555555 := by
        have : m ≥ 18 := h2
        have h4 : ∀ k, seq (17 + k) ≥ 555555555555555555 := by
          intro k
          induction k with
          | zero =>
            norm_num [seq]
          | succ k ih =>
            have h5 : seq (17 + (k + 1)) = seq (17 + k) * 10 + 5 := by
              simp [seq]
            rw [h5]
            omega
        have h5 : m ≥ 17 := by omega
        have h6 : m - 17 ≥ 1 := by omega
        have h7 : seq m ≥ 555555555555555555 := by
          have h8 : m = 17 + (m - 17) := by omega
          rw [h8]
          apply h4 (m - 17)
        linarith
      have h4 : n ≥ 555555555555555555 := by linarith [h3, hm_eq]
      linarith

    interval_cases m <;> norm_num [seq] at hm_eq hm_div <;> omega