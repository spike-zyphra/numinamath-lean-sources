import Mathlib

theorem number_theory_268866 (n : ℤ) :
  IsSquare (n^2 + 59 * n + 881) ↔ n = -40 ∨ n = -19 := by
  constructor
  · -- Assume $n^2 + 59n + 881$ is a perfect square, prove $n = -40 \lor n = -19$.
    intro h
    rcases h with ⟨m, hm⟩
    have h1 : (2 * m - (2 * n + 59)) * (2 * m + (2 * n + 59)) = 43 := by
      nlinarith
    -- Since 43 is prime, the pairs of factors are (1, 43), (-1, -43), (43, 1), (-43, -1)
    have h3 : (2 * m - (2 * n + 59)) = 1 ∨ (2 * m - (2 * n + 59)) = 43 ∨
      (2 * m - (2 * n + 59)) = -1 ∨ (2 * m - (2 * n + 59)) = -43 := by
      have h4 : (2 * m - (2 * n + 59)) ∣ 43 := by
        use (2 * m + (2 * n + 59))
        all_goals nlinarith
      have h5 : (2 * m - (2 * n + 59)) ≤ 43 := by
        apply Int.le_of_dvd (by norm_num) h4
      have h6 : (2 * m - (2 * n + 59)) ≥ -43 := by
        have h7 : -(2 * m - (2 * n + 59)) ∣ 43 := by
          exact Int.neg_dvd.2 h4
        have h8 : -(2 * m - (2 * n + 59)) ≤ 43 := by
          apply Int.le_of_dvd (by norm_num) h7
        omega
      interval_cases h : (2 * m - (2 * n + 59)) <;> tauto
    rcases h3 with (h3 | h3 | h3 | h3)
    · -- Case $2m - (2n + 59) = 1$.
      have h4 : 2 * m + (2 * n + 59) = 43 := by
        rw [h3] at h1
        nlinarith
      have hm1 : m = 11 := by
        omega
      have hn1 : n = -19 := by
        omega
      right
      exact hn1
    · -- Case $2m - (2n + 59) = 43$.
      have h4 : 2 * m + (2 * n + 59) = 1 := by
        rw [h3] at h1
        nlinarith
      have hm2 : m = 11 := by
        omega
      have hn2 : n = -40 := by
        omega
      left
      exact hn2
    · -- Case $2m - (2n + 59) = -1$.
      have h4 : 2 * m + (2 * n + 59) = -43 := by
        rw [h3] at h1
        nlinarith
      have hm3 : m = -11 := by
        omega
      have hn3 : n = -40 := by
        omega
      left
      exact hn3
    · -- Case $2m - (2n + 59) = -43$.
      have h4 : 2 * m + (2 * n + 59) = -1 := by
        rw [h3] at h1
        nlinarith
      have hm4 : m = -11 := by
        omega
      have hn4 : n = -19 := by
        omega
      right
      exact hn4
  · -- Assume $n = -40 \lor n = -19$, prove $n^2 + 59 * n + 881$ is a perfect square.
    rintro (h | h)
    · -- Case $n = -40$.
      rw [show n = -40 by linarith [h]]
      use 11
      norm_num
    · -- Case $n = -19$.
      rw [show n = -19 by linarith [h]]
      use 11
      norm_num