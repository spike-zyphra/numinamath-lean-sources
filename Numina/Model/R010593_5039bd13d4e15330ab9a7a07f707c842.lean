import Mathlib

theorem number_theory_4634 (h : numfirst + numsecond + numstandby = 69 ∧
    70 * numfirst + 55 * numsecond + 39 * numstandby = 3274) :
    numfirst=9 ∧numsecond=19 ∧ numstandby=41 := by 
  rcases h with ⟨h1, h2⟩
  have hf : numfirst = 9 := by
    omega
  have hs : numsecond = 19 := by
    omega
  have hst : numstandby = 41 := by
    omega
  exact ⟨hf, hs, hst⟩