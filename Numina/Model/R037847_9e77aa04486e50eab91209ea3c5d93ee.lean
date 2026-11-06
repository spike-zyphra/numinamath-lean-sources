import Mathlib

theorem number_theory_217250 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (p : Polynomial ℤ) (hp : ∀ x : ℤ, p.eval x ≡ 0 [ZMOD a] ∧ p.eval x ≡ 0 [ZMOD b]) :
    ∃ z, p.eval z ≡ 0 [ZMOD Int.lcm a b] := by
  use 0 
  have h1 := hp 0
  rcases h1 with ⟨ha0, hb0⟩ 
  have h1' : (p.eval (0 : ℤ) : ℤ) % a = 0 := by 
    simpa [Int.ModEq] using ha0
  have h2' : (p.eval (0 : ℤ) : ℤ) % b = 0 := by 
    simpa [Int.ModEq] using hb0
  have h3 : (p.eval (0 : ℤ) : ℤ) % (Int.lcm a b) = 0 := by
    have h4 : (p.eval (0 : ℤ) : ℤ) % a = 0 := h1'
    have h5 : (p.eval (0 : ℤ) : ℤ) % b = 0 := h2'
    have h5' : a ∣ p.eval (0 : ℤ) := by 
      exact Int.dvd_of_emod_eq_zero h4
    have h6' : b ∣ p.eval (0 : ℤ) := by 
      exact Int.dvd_of_emod_eq_zero h5
    have h8 : (Int.lcm a b : ℤ) ∣ (p.eval (0 : ℤ)) := by 
      apply Int.lcm_dvd 
      all_goals 
        try exact h5'
        try exact h6'
    have h7' : (p.eval (0 : ℤ)) % (Int.lcm a b) = 0 := by 
      exact Int.emod_eq_zero_of_dvd h8
    exact h7'
  show (p.eval (0 : ℤ) : ℤ) ≡ 0 [ZMOD Int.lcm a b]
  simp [Int.ModEq, h3]