import Mathlib

/-
3-5. Determine the maximum value of the ratio of a three-digit number to the number equal to the sum of the digits of this number.
-/

theorem number_theory_284735:
IsGreatest {x : ℝ | ∃ a b c : ℕ, 1≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧ 0 ≤ c ∧ c≤ 9 ∧ x = (100*(a:ℝ)+10*(b:ℝ)+(c:ℝ)) / ((a:ℝ)+(b:ℝ)+(c:ℝ))} 100 := by
  unfold IsGreatest
  simp [upperBounds]

  --100 can be achieved. Just use 100.
  constructor
  use 1
  simp
  use 0
  simp
  use 0
  simp

  intro r a la ua b ub c uc h

  --100 is an upper bound, since 100a + 10b +c ≤ 100a + 100b + 100c. 
  have tar: (100 * (a:ℝ) + 10 * b + c) ≤ 100 * (a + b + c) := by linarith
  have : 0<(a:ℝ)+b+c := by positivity
  field_simp [h]
  rw [div_le_iff₀]
  exact tar
  exact this
  
  
