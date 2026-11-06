import Mathlib

open Polynomial 

theorem algebra_608607 {b : ℤ}: 
  (∃ (f : Polynomial ℤ), (f.eval 2 = 2010 ∧ f.eval b = 8) )↔ (b - 2) ∣ -2002 := by 
  constructor 
  · -- Forward direction: (∃ f, f(2) = 2010 ∧ f(b) = 8) → (b - 2) ∣ -2002
    rintro ⟨f, h1, h2⟩ 
    rw [show (-2002 : ℤ) = 8 - 2010 by norm_num]
    rw [← h1, ← h2]
    apply Polynomial.sub_dvd_eval_sub 
  · -- Reverse direction: (b - 2) ∣ -2002 → (∃ f, f(2) = 2010 ∧ f(b) = 8) 
    intro h
    have h1 : (b - 2 : ℤ) ∣ (-2002 : ℤ) := h 
    obtain ⟨c, hc⟩ := h1 
    use Polynomial.C (c) * (X - Polynomial.C (2 : ℤ)) + Polynomial.C (2010 : ℤ)
    constructor 
    · -- Show that f.eval 2 = 2010 
      simp
    · -- Show that f.eval b = 8
      simp
      <;> ring_nf
      <;> norm_num 
      all_goals try { nlinarith [hc] }