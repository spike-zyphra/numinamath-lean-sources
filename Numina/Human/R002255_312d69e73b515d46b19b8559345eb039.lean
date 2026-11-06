import Mathlib

/-
The minimum value of the quotient of a (base ten) number of three different nonzero digits divided by the sum of its digits is

$\textbf{(A) }9.7\qquad\textbf{(B) }10.1\qquad\textbf{(C) }10.5\qquad\textbf{(D) }10.9\qquad \textbf{(E) }20.5$
-/

theorem number_theory_77607:
IsLeast {r | ∃x a b c :ℕ, x = 100*a+10*b+c ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9  ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ r=(x:ℚ)/(a+b+c)} (10.5) := by
  
  unfold IsLeast lowerBounds
  simp

  constructor

  --189 gives 10.5 as quotient, so this minimum value is at most 10.5.
  use 189, 1, 8, 9
  simp
  norm_num

  --For the other direction, we show the quotients are always at least 10.5.
  intro r x a b c hx ane0 bne0 cne0 ale9 ble9 cle9 aneb bnec anec hr
  rw [hx] at hr
  rw [hr]
  have abcpos : 0 < a + b + c := by omega
  have abcrpos : 0 < (a:ℚ) + b + c := by norm_cast
  
  --Rewrite this and we get that we need a to be small and b c be large. This will suggest a bound on the quotient.
  have : 10.5 * ((a:ℚ)+b+c) ≤ (100*a+10*b+c) := by 
    ring_nf
    field_simp

    

    have : ((-(179:ℚ))*(a:ℚ)) + (b:ℚ) + (19:ℚ) * (c:ℚ) ≤ 0 := by 
      have : b + 19 * c ≤ 179 * a := by omega
      qify at this
      linarith



    nlinarith
  field_simp at this ⊢
  exact (le_div_iff₀ abcrpos).mpr this

  
  
  
