import Mathlib

theorem number_theory_137207 (n : ℕ) (h : n = 2345678) :
    IsLeast {d | d ∈ Nat.digits 10 n ∧ (Nat.ofDigits 10 (List.filter (fun x => x ≠ d) (Nat.digits 10 n))) % 9 = 0} 8 := by
  rw [h]
  constructor
  · -- Show 8 is in the set
    constructor 
    · -- Show 8 is in the digits
      simp [Nat.digits, Nat.digitsAux]
    · -- Show removing 8 results in a number divisible by 9
      native_decide
  · -- Show 8 is the least element
    intro d h 
    rcases h with ⟨hd, hdiv⟩ 
    norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at hd hdiv ⊢ 
    rcases hd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- d = 8 
      all_goals omega
    · -- d = 7 
      all_goals try { 
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux, List.filter] at hdiv ⊢ 
        }
    · -- d = 6
      all_goals try { 
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux, List.filter] at hdiv ⊢ 
        }
    · -- d = 5
      all_goals try { 
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux, List.filter] at hdiv ⊢ 
        }
    · -- d = 4 
      all_goals try { 
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux, List.filter] at hdiv ⊢ 
        }
    · -- d = 3 
      all_goals try { 
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux, List.filter] at hdiv ⊢ 
        }
    · -- d = 2 
      all_goals try { 
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux, List.filter] at hdiv ⊢ 
        }