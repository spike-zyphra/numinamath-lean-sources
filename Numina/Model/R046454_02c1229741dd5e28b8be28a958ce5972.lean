import Mathlib



theorem number_theory_11193{seq1 seq2:ℕ → ℕ}
  (hseq1: seq1 = fun n => 1+6*n)(hseq2: seq2 = fun n => 4+7*n) :
  IsGreatest {x | ∃ m n, x = seq1 m ∧ x = seq2 n ∧ 1 ≤ x ∧ x ≤ 100} 67
  := by
  rw [IsGreatest, upperBounds]; simp
  constructor
  ·
    rw [hseq1, hseq2]; simp; constructor
    use 11; use 9
  ·
    intro m n hs12 ge1 le100
    have h1: seq1 m = 1+6*m := by rw [hseq1]
    have h2: seq2 n = 4+7*n := by rw [hseq2]
    rw [h1] at hs12; rw [h2] at hs12;
    have eqs : (1 + 6 * m : ℕ) = (4 + 7 * n : ℕ) := by
      omega
    have h3 : m ≥ 4 := by
      omega
    have h4 : n ≥ 3 := by
      omega
    have h5 : (1 + 6 * m : ℕ) = (1 + 6 * m : ℕ) := by
      rfl
    have h6 : m ≤ 16 := by
      omega
    interval_cases m <;> try { 
      omega
    } <;> try { 
      interval_cases n <;> omega 
    }