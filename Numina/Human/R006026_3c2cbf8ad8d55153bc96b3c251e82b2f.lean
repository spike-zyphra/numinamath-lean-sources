import Mathlib
/- How many ordered pairs of integers (a,b) satisfy all of the following inequalities?

$$
\begin{aligned}
a^{2}+b^{2} & <16 \\
a^{2}+b^{2} & <8 a \\
a^{2}+b^{2} & <8 b
\end{aligned}
$$ -/
theorem algebra_611191 : {(a, b) : ℤ × ℤ | a ^ 2 + b ^ 2 < 16 ∧ a ^ 2 + b ^ 2 < 8 * a ∧ a ^ 2 + b ^ 2 < 8 * b}.ncard = 6:= by

  -- Proves that the set equals exactly these 6 pairs: (1,1), (1,2), (2,1), (2,2), (3,2), (2,3)
  have h1 : {(a, b) : ℤ × ℤ | a ^ 2 + b ^ 2 < 16 ∧ a ^ 2 + b ^ 2 < 8 * a ∧ a ^ 2 + b ^ 2 < 8 * b} = {(1, 1), (1, 2), (2, 1), (2, 2), (3, 2), (2, 3)}:= by
    ext ⟨a, b⟩
    constructor
    .
      intro h
      simp at h
      rcases h with ⟨h1, h2, h3⟩
      -- Rearranging inequalities to more useful forms
      replace h2 : (a - 4) ^ 2 + b ^ 2 < 16:= by linarith
      replace h3 : (b - 4) ^ 2 + a ^ 2 < 16:= by linarith

      -- Proves that 1 ≤ a ≤ 3 by contradiction
      have h4 : 1 ≤ a ∧ a ≤ 3:= by
        by_contra H
        simp at H
        by_cases h4 : a ≤ 0
        .
          have g1 : (a - 4) ^ 2 ≥ 16:= by nlinarith only [h4]
          have g2 : b ^ 2 ≥ 0:= by positivity
          linarith
        .
          simp at h4
          replace H:= H (by omega)
          replace H : a ≥ 4:= by omega
          replace H : a ^ 2 ≥ 16:= by nlinarith only [H]
          have g2 : b ^ 2 ≥ 0:= by positivity
          linarith

      -- Proves that 1 ≤ b ≤ 3 by contradiction
      have h5 : 1 ≤ b ∧ b ≤ 3:= by
        by_contra H
        simp at H
        by_cases h5 : b ≤ 0
        .
          have g1 : (b - 4) ^ 2 ≥ 16:= by nlinarith only [h5]
          have g2 : a ^ 2 ≥ 0:= by positivity
          linarith
        .
          simp at h5
          replace H:= H (by omega)
          replace H : b ≥ 4:= by omega
          replace H : b ^ 2 ≥ 16:= by nlinarith only [H]
          have g2 : a ^ 2 ≥ 0:= by positivity
          linarith

      -- Converts bounds to exact possible values
      replace h4 : a = 1 ∨ a = 2 ∨ a = 3:= by omega
      replace h5 : b = 1 ∨ b = 2 ∨ b = 3:= by omega

      -- Case analysis on all possible values of a and b
      rcases h4 with h4 | h4 | h4
      .
        rcases h5 with h5 | h5 | h5
        .
          subst a b
          simp
        .
          subst a b
          simp
        .
          subst a b
          by_contra _
          simp at h2
      .
        rcases h5 with h5 | h5 | h5
        all_goals
          subst a b
          simp
      .
        rcases h5 with h5 | h5 | h5
        .
          subst a b
          by_contra _
          simp at h3
        .
          subst a b
          simp
        .
          by_contra _
          subst a b
          simp at h1
    .
      -- Proves the reverse direction: all listed pairs satisfy the inequalities
      intro h
      simp at h
      rcases h with h | h | h | h | h | h
      all_goals
        rcases h with ⟨h1 ,h2⟩
        subst a b
        simp

  -- Final steps to prove the cardinality is 6
  rw [h1]
  rw [show ({(1, 1), (1, 2), (2, 1), (2, 2), (3, 2), (2, 3)} : Set (ℤ × ℤ)) = ({(1, 1), (1, 2), (2, 1), (2, 2), (3, 2), (2, 3)} : Finset (ℤ × ℤ)) by simp]
  rw [Set.ncard_coe_Finset]
  repeat rw [Finset.card_insert_of_not_mem]
  all_goals
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    by_contra H
    trivial
