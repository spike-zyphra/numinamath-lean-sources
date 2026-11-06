import Mathlib

open Nat

theorem number_theory_23099 (s : Finset ℕ) (hs : s = (Finset.Icc 1 8).image fun n =>
    n ! + (n + 1) !) (a b : ℕ) (hlcm : Finset.lcm s id = a * b !) (hb : ¬b + 1 ∣ a) :
    a + b = 11 := by
  have h1 : s = {3, 8, 30, 144, 840, 5760, 45360, 403200} := by 
    rw [hs]
    native_decide
  have h2 : Finset.lcm s id = 3628800 := by
    rw [h1]
    native_decide
  rw [h2] at hlcm 
  have h3 : a * b ! = 3628800 := by
    linarith 
  have h4 : b ≤ 10 := by
    by_contra h 
    push_neg at h 
    have h5 : b ! ≥ 11 ! := by 
      apply Nat.factorial_le 
      omega 
    have h6 : 11 ! = 39916800 := by 
      norm_num [Nat.factorial] 
    have h7 : b ! ≥ 39916800 := by 
      linarith [h5, h6] 
    have h9 : a * b ! = 3628800 := h3 
    have h10 : a = 0 := by 
      nlinarith [show 0 < (b ! : ℕ) by 
        apply Nat.factorial_pos 
      ]
    rw [h10] at h3 
    all_goals 
      nlinarith 
  have h4 : b ≤ 10 := h4 
  interval_cases b <;> try { 
    simp [Nat.factorial] at h3 
    all_goals 
      try { 
        omega 
      } 
      <;> try { 
        all_goals 
          try { 
            have h9 : a ≤ 3628800 := by 
              nlinarith 
            interval_cases a <;> norm_num at h3 <;> omega 
          } 
      }
  }
  all_goals 
    omega