import Mathlib

open Real Set
open scoped BigOperators

/- 3. (CAN) Find the minimum value of
$$
\max (a+b+c, b+c+d, c+d+e, d+e+f, e+f+g)
$$
subject to the constraints
(i) $a, b, c, d, e, f, g \geq 0$.
(ii) $a+b+c+d+e+f+g=1$. -/
theorem inequalities_280406 :
  IsLeast {x : ℝ | ∃ a b c d e f g : ℝ,
    a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ e ≥ 0 ∧ f ≥ 0 ∧ g ≥ 0 ∧
    a + b + c + d + e + f + g = 1 ∧
    x = max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g)} (1 / 3) := by

  constructor
  · -- Let's prove that 1/3 belongs to our set
    use 1 / 3, 0, 0, 1 / 3, 0, 0, 1 / 3
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num 
  · -- Now, we need to prove that 1/3 is the least element of our set
    intro x h
    -- Extract all variables and hypotheses from our assumption
    rcases h with ⟨a, b, c, d, e, f, g, _, hb, hc, _, _, _, _, hsum, hx⟩

    -- Prove that x is greater than or equal to the first sum (a+b+c)
    have h1 : x ≥ a + b + c := by
      rw [hx]
      apply le_max_of_le_left
      apply le_max_of_le_left
      apply le_max_of_le_left
      apply le_max_of_le_left
      all_goals linarith

    -- Prove that x is greater than or equal to the second sum (b+c+d)
    have h2 : x ≥ b + c + d := by
      rw [hx]
      apply le_max_of_le_left
      apply le_max_of_le_left
      apply le_max_of_le_left
      apply le_max_of_le_right
      all_goals linarith

    -- Prove that x is greater than or equal to the fifth sum (e+f+g)
    have h5 : x ≥ e + f + g := by
      rw [hx]
      apply le_max_of_le_right
      all_goals linarith

    -- Use nonlinear arithmetic to complete the proof
    nlinarith
