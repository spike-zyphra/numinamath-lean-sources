import Mathlib

theorem number_theory_131810 (p : ℕ) (hp : Nat.Prime p) :
    ∃ x : ℚ, 2*x^3-2*p*x^2+(1-p)*x+p=0 ↔ p=2 := by
  use 2
  constructor
  · -- Assume $2 * (2)^3 - 2 * p * (2)^2 + (1-p) * 2 + p = 0$, conclude $p = 2$.
    intro h
    have eq1 : (2 : ℚ) ^ 3 = (8 : ℚ) := by norm_num
    have eq2 : (2 : ℚ) ^ 2 = (4 : ℚ) := by norm_num
    ring_nf at h -- To simplify the equation to $18 - 9p = 0$
    have eq3 : (p : ℚ) = 2 := by
      nlinarith 
    -- Convert from rational to natural
    have eq4 : p = 2 := by exact_mod_cast eq3
    tauto
  · -- Assume $p = 2$, prove $2 * (2)^3 - 2 * p * (2)^2 + (1-p) * 2 + p = 0$.
    intro h
    rw [h]
    norm_num