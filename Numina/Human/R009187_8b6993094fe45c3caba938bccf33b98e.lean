import Mathlib

/- In year N, the 300th day of the year is a Tuesday. 
In year N+1, the 200th day is also a Tuesday. 
On what day of the week did the 100th day of year N−1 occur?
(A) Thursday(B) Friday(C) Saturday(D) Sunday(E) Monday -/

theorem number_theory_93551 (N : ℤ) (oneJan : ℤ → ZMod 7) (next : ℤ → ZMod 7)
  (h300 : oneJan N + 299 = 2)  -- 300th day of year N is Tuesday 
  (h200 : oneJan (N + 1) + 199 = 2)  -- 200th day of year N+1 is Tuesday
  (h : ∀ n : ℤ, oneJan (n + 1) = oneJan n + 365 + next n) --implicit hypothesis of a calendar
  (hnext : ∀ n : ℤ, (next n = 0 ∨ next n = 1) ∧ ∀ j k : ℤ, next j = 1 → (next k = 1 ↔ (k - j) % 4 = 0)) : --implicit hypothesis of a calendar 
  oneJan (N - 1) + 99 = 4 := by 
    have h_copy : ∀ n : ℤ, oneJan (n + 1) = oneJan n + 365 + next n := by exact h
    
    specialize h N
    rw[h] at h200
    --N+1 is a leap year
    have hhN : next N = 1 := by
      have hhN : oneJan N = 2 - 5 := by exact eq_sub_of_add_eq h300
      ring_nf at hhN
      rw[hhN] at h200
      ring_nf at h200
      have hhN' : next N = 2 - 561 := by exact eq_sub_of_add_eq' h200
      ring_nf at hhN'
      congr
    --then N is not a leap year and neither is N-1
    have hPreN : next (N - 1) = 0 := by 
      specialize hnext (N - 1)
      obtain ⟨h1|h2,h3⟩:= hnext
      · exact h1
      · specialize h3 N (N - 1)
        specialize h3 hhN
        rw[h3] at h2
        ring_nf at h2
        contradiction
    --then one is able by modular arithmetic calculation to determine that the 100th day of N-1 is a Thursday
    specialize h_copy (N - 1)
    simp at h_copy
    rw[h_copy, hPreN] at h300
    have h300' : oneJan (N - 1) + 1 + 0 + 5 = 2 := by congr
    norm_num at h300'
    rw[add_assoc] at h300'
    have hh: oneJan (N - 1) = 2 - (1 + 5):= by exact eq_sub_of_add_eq h300'
    norm_num at hh
    rw[hh]
    norm_num
    congr