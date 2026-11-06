import Mathlib

def triangular_number (n : ℕ) := n * (n + 1) / 2

theorem number_theory_276682 :
    IsLeast {y | ∃ n, triangular_number n = y ∧ y ≥ 2000} 2016 := by
  constructor
  · -- Show 2016 is in the set.
    use 63
    all_goals
      norm_num [triangular_number]
  · -- Show there is no smaller y in the set.
    intro y hy
    rcases hy with ⟨n, hn1, hn2⟩
    by_contra h
    push_neg at h
    -- Now we have y < 2016 and y ≥ 2000
    -- So we have found a triangular number in [2000, 2015]
    -- Let's prove that this is impossible
    have h1 : n * (n + 1) / 2 < 2016 := by
      have h3 : n * (n + 1) / 2 = y := by
        rw [triangular_number] at hn1 
        omega
      omega
    have h2 : n * (n + 1) < 4032 := by
      by_contra h7
      push_neg at h7
      have h70 : n * (n + 1) ≥ 4032 := by omega
      have h71 : n * (n + 1) / 2 ≥ 2016 := by
        omega
      omega
    -- Now we know n is bounded
    have h3 : n ≤ 62 := by 
      nlinarith
    interval_cases n <;> norm_num [triangular_number] at hn1 hn2 <;> omega