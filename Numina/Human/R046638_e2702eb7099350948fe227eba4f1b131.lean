import Mathlib
/- ## Problem A1

Find all integer solutions to: $a+b+c=24, a^{2}+b^{2}+c^{2}=210, a b c=440$. -/
theorem algebra_211673 : {(a, b, c) : ℤ × ℤ × ℤ | a + b + c = 24 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 210 ∧ a * b * c = 440} = {(5, 8, 11), (5, 11, 8), (8, 5, 11), (8, 11, 5), (11, 5, 8), (11, 8, 5)}:= by
  -- We use extensionality to prove equality of sets
  ext ⟨a, b, c⟩
  constructor
  -- Forward direction: if (a,b,c) satisfies the system, then it's one of the listed solutions
  .
    intro h
    simp at h
    rcases h with ⟨h1, h2, h3⟩
    -- Derive that ab + bc + ca = 183 using the identity (a+b+c)² = a²+b²+c²+2(ab+bc+ca)
    replace h2 : a * b + b * c + c * a = 183:= by
      replace h1 : (a + b + c) ^ 2 = 24 ^ 2:= by rw [h1]
      linarith
    -- Show that each solution must have values from {5,8,11}
    -- by proving (a-5)(b-5)(c-5) = 0, (a-8)(b-8)(c-8) = 0, and (a-11)(b-11)(c-11) = 0
    have g1 : (a - 5) * (b - 5) * (c - 5) = 0:= by linarith
    have g2 : (a - 8) * (b - 8) * (c - 8) = 0:= by linarith
    have g3 : (a - 11) * (b - 11) * (c - 11) = 0:= by linarith
    simp at g1
    -- Case analysis on which value equals 5
    rcases g1 with ⟨g1 | g1⟩ | g1
    -- Case: a = 5
    .
      replace g1 : a = 5:= by linarith
      subst a
      simp at g2
      -- Case analysis on which value equals 8
      rcases g2 with g2 | g2
      -- Case: b = 8, which forces c = 11
      .
        replace g2 : b = 8:= by linarith
        subst b
        simp at g3
        replace g3 : c = 11:= by linarith
        subst c
        simp
      -- Case: c = 8, which forces b = 11
      .
        replace g2 : c = 8:= by linarith
        subst c
        simp at g3
        replace g3 : b = 11:= by linarith
        subst b
        simp
    -- Case: b = 5
    .
      replace g1 : b = 5:= by linarith
      subst b
      simp at g2
      -- Case analysis on which value equals 8
      rcases g2 with g2 | g2
      -- Case: a = 8, which forces c = 11
      .
        replace g2 : a = 8:= by linarith
        subst a
        simp at g3
        replace g3 : c = 11:= by linarith
        subst c
        simp
      -- Case: c = 8, which forces a = 11
      .
        replace g2 : c = 8:= by linarith
        subst c
        simp at g3
        replace g3 : a = 11:= by linarith
        subst a
        simp
    -- Case: c = 5
    .
      replace g1 : c = 5:= by linarith
      subst c
      simp at g2
      -- Case analysis on which value equals 8
      rcases g2 with g2 | g2
      -- Case: a = 8, which forces b = 11
      .
        replace g2 : a = 8:= by linarith
        subst a
        simp at g3
        replace g3 : b = 11:= by linarith
        subst b
        simp
      -- Case: b = 8, which forces a = 11
      .
        replace g2 : b = 8:= by linarith
        subst b
        simp at g3
        replace g3 : a = 11:= by linarith
        subst a
        simp
  -- Reverse direction: verify that each of the listed solutions satisfies the system
  .
    intro h
    simp at h
    -- Case analysis on which permutation we have
    rcases h with h | h | h | h | h | h
    -- For each permutation, substitute the values and verify the equations
    all_goals
      rcases h with ⟨h1, h2, h3⟩
      subst a b c
      simp
