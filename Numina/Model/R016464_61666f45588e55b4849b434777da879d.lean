import Mathlib

theorem number_theory_110891 (n : ℕ) (h₀ : n < 100) :
    (∀ i ∈ Finset.Icc 2 12, (27700 + n) % i = 0) ↔ n = 20 := by
  constructor
  · -- Assume ∀ i ∈ [2, 12], (27700 + n) % i = 0
    intro h
    have h1 : (27700 + n) % 2 = 0 := by
      apply h
      norm_num
    have h3 : (27700 + n) % 3 = 0 := by
      apply h
      norm_num
    have h4 : (27700 + n) % 4 = 0 := by
      apply h
      norm_num
    have h5 : (27700 + n) % 5 = 0 := by
      apply h
      norm_num
    have h6 : (27700 + n) % 6 = 0 := by
      apply h
      norm_num
    have h7 : (27700 + n) % 7 = 0 := by
      apply h
      norm_num
    have h8 : (27700 + n) % 8 = 0 := by
      apply h
      norm_num
    have h9 : (27700 + n) % 9 = 0 := by
      apply h
      norm_num
    have h10 : (27700 + n) % 10 = 0 := by
      apply h
      norm_num
    have h11 : (27700 + n) % 11 = 0 := by
      apply h
      norm_num
    have h12 : (27700 + n) % 12 = 0 := by
      apply h
      norm_num
    interval_cases n <;> omega
  · -- Assume n = 20
    intro h
    rw [h]
    intro i hi
    rw [Finset.mem_Icc] at hi
    rcases hi with ⟨hi1, hi2⟩
    interval_cases i <;> norm_num