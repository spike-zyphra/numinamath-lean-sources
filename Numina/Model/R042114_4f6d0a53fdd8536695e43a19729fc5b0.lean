import Mathlib

open Nat

theorem number_theory_8091 {f : ℕ → ℕ}
    (hf : ∀ a > 0, IsLeast {p | p.Prime ∧ p ∣ a} (f a)) :
    f 35 = f 55 := by
  have h1 : f 35 = 5 := by 
    have h11 : f 35 ∈ {p | p.Prime ∧ p ∣ 35} := by 
      apply (hf 35 (by norm_num)).left
    have h12 : ∀ p, (p ∈ {p | p.Prime ∧ p ∣ 35}) → f 35 ≤ p := by 
      apply (hf 35 (by norm_num)).right
    have h5_in_set : (5 ∈ {p | p.Prime ∧ p ∣ 35}) := by 
      constructor 
      · norm_num 
      · norm_num 
    have h13 : f 35 ≤ 5 := by 
      specialize h12 5 h5_in_set 
      linarith 
    have h14 : f 35 = 5 ∨ f 35 = 7 := by 
      have h15 : f 35 ∣ 35 := by 
        have h151 : f 35 ∈ {p | p.Prime ∧ p ∣ 35} := h11
        simp at h151 ⊢ 
        tauto 
      have h16 : f 35 ≤ 35 := by 
        exact Nat.le_of_dvd (by norm_num) h15 
      interval_cases h : f 35 <;> norm_num at h15 ⊢ 
      <;> try { tauto } <;> norm_num [Nat.Prime] at h11 ⊢ 
      <;> try { tauto } <;> nlinarith 
    rcases h14 with (h14 | h14) 
    · linarith 
    · exfalso 
      linarith 
  have h2 : f 55 = 5 := by 
    have h41 : f 55 ∈ {p | p.Prime ∧ p ∣ 55} := by 
      apply (hf 55 (by norm_num)).left
    have h42 : ∀ p, (p ∈ {p | p.Prime ∧ p ∣ 55}) → f 55 ≤ p := by 
      apply (hf 55 (by norm_num)).right 
    have h5_in_set_55 : (5 ∈ {p | p.Prime ∧ p ∣ 55}) := by 
      constructor 
      · norm_num 
      · norm_num 
    have h43 : f 55 ≤ 5 := by 
      specialize h42 5 h5_in_set_55 
      linarith 
    have h44 : f 55 = 5 ∨ f 55 = 11 := by 
      have h45 : f 55 ∣ 55 := by 
        have h451 : f 55 ∈ {p | p.Prime ∧ p ∣ 55} := h41
        simp at h451 ⊢ 
        tauto 
      have h46 : f 55 ≤ 55 := by 
        exact Nat.le_of_dvd (by norm_num) h45 
      interval_cases h : f 55 <;> norm_num at h45 ⊢ 
      <;> try { tauto } <;> norm_num [Nat.Prime] at h41 ⊢ 
      <;> try { tauto } <;> nlinarith 
    rcases h44 with (h44 | h44) 
    · linarith 
    · exfalso 
      linarith 
  linarith [h1, h2]