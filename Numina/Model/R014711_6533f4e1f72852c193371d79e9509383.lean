import Mathlib

def isHopeNumber (n : ℕ) := Odd (Nat.divisors n).card

theorem number_theory_121212 :
    IsGreatest {n | n ∈ Finset.Icc 1 1000 ∧ isHopeNumber n} 961 := by
  constructor
  · -- Show 961 is in the set
    constructor
    · -- Show 961 ∈ [1, 1000]
      simp [Finset.mem_Icc]
    · -- Show 961 is a Hope Number
      unfold isHopeNumber
      have h1 : (Nat.divisors 961).card = 3 := by 
        native_decide
      rw [h1]
      exact Nat.odd_iff.mpr (by norm_num)
  · -- Show there is no greater element in the set
    intro n hn
    rcases hn with ⟨hn1, h2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hnle1, hnnen1000⟩
    by_contra h
    push_neg at h 
    unfold isHopeNumber at h2
    have h3 : n > 961 := by omega 
    have h4 : n ≤ 1000 := by omega 
    have h5 : ¬ Odd (Nat.divisors n).card := by
      have h6 : n > 961 := h3 
      have h7 : n ≤ 1000 := h4 
      interval_cases n <;> try { native_decide } 
    contradiction