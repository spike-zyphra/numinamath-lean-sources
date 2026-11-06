import Mathlib


open Nat Finset


theorem number_theory_136497 :
    IsLeast {b : ℕ | ∃ a : Fin 4 → ℕ, StrictMono a ∧ (∀ i j, i ≠ j → Nat.gcd (a i) (a j) > 1) ∧ Nat.gcd (a 0) (Nat.gcd (a 1) (Nat.gcd (a 2) (a 3))) = 1 ∧ a 3 = b} 15 := by
  constructor 
  · -- Show that 15 is achievable 
    use λ i => 
      match i with 
      | 0 => 6 
      | 1 => 10 
      | 2 => 12
      | 3 => 15 
      | _ => 0
    constructor
    · -- Show that a is strictly increasing 
      intro i j h 
      fin_cases i <;> fin_cases j <;> simp at *
      all_goals omega 
    constructor 
    · -- Show that for any i j with i ≠ j, gcd(a i, a j) > 1
      intro i j h_ineq
      fin_cases i <;> fin_cases j <;> simp at * 
      all_goals norm_num [Nat.gcd]
      all_goals omega 
    constructor 
    · -- Show gcd(a 0, gcd(a 1, gcd(a 2, a 3))) = 1 
      norm_num [Nat.gcd]
      all_goals omega 
    · -- Show a 3 = 15 
      simp 
  · -- Show that 15 is minimal 
    intro b hb
    rcases hb with ⟨a, ha1, ha2, ha3, ha4⟩ 
    by_contra h
    push_neg at h
    have h1 : a 0 < a 1 := by
      apply ha1
      simp 
      <;> omega
    have h2 : a 1 < a 2 := by
      apply ha1
      simp 
    have h3 : a 2 < a 3 := by 
      apply ha1
      simp 
    have h4 : a 3 = b := by
      omega 
    have h55 : b < 15 := by omega 
    have h6 := ha2 0 1 (by simp)
    have h7 := ha2 0 2 (by simp)
    have h8 := ha2 0 3 (by simp)
    have h9 := ha2 1 2 (by simp)
    have h10 := ha2 1 3 (by simp)
    have h11 := ha2 2 3 (by simp)
    have h12 : Nat.gcd (a 0) (Nat.gcd (a 1) (Nat.gcd (a 2) (a 3))) = 1 := ha3 
    have h16 : a 3 < 15 := by omega 
    have h17 : a 2 < 14 := by 
      omega 
    have h18 : a 1 < 13 := by 
      omega 
    have h19 : a 0 < 12 := by
      omega 
    interval_cases a 0 <;> norm_num at h6 h7 h8 <;> try { 
      omega 
    } <;> interval_cases a 1 <;> norm_num at h6 h9 h10 <;> try { 
      omega 
    } <;> interval_cases a 2 <;> norm_num at h7 h9 h11 <;> try { 
      omega 
    } <;> interval_cases a 3 <;> norm_num [Nat.gcd] at h6 h7 h8 h9 h10 h11 h12 <;> try { 
      omega 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        native_decide 
      }
    } <;> try { 
      tauto 
      <;> nlinarith <;> try { native_decide }
    }
    <;> norm_num [Nat.gcd] at h6 h7 h8 h9 h10 h11 h12
    <;> try { 
      omega 
      <;> try { 
        nlinarith <;> try { native_decide }
      }
    }
    <;> try { 
      omega 
      <;> try { 
        nlinarith <;> try { native_decide }
      }
    }