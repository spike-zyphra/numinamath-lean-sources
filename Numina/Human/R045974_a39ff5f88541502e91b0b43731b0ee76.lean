import Mathlib

/- ## Task $1 / 86$

We are looking for the smallest natural number $n$, which is the product of 3 prime factors $p_{1} ; p_{2} ; p_{3}$, and it holds that: $p_{3}=55 \cdot p_{1} \cdot p_{2}+1$ and $p_{3}>p_{2}>p_{1}$. -/
theorem number_theory_160444 (A : Set ℕ)(hA : A = {n |∃ p1 p2 p3 : ℕ, p1.Prime ∧ p2.Prime ∧ p3.Prime ∧ n = p1 * p2 * p3 ∧ p3 = 55 * p1 * p2 + 1 ∧ p1 < p2 ∧ p2 < p3}):1986 ∈ A ∧ ∀ n ∈ A, n ≥ 1986 := by
  constructor
  -- -- Show that 1986 is in the set A
  · rw [hA]
    simp
    use 2
    constructor
    · norm_num
    · use 3
      constructor
      · norm_num
      · use 331
        constructor
        · norm_num
        · constructor
          · norm_num
          · constructor
            · norm_num
            · constructor
              · norm_num
              · norm_num
  -- -- Prove that 1986 is the smallest number in the set A
  · intro n hn
    rw [hA] at hn
    simp at hn
    rcases hn with ⟨p1,⟨hp1,⟨p2,⟨hp2,⟨p3,⟨hp3,⟨hn,⟨hp,⟨hlt1, hlt2⟩⟩⟩⟩⟩⟩⟩⟩⟩
    -- Establish lower bounds for p1, p2, and p3
    have : p1 ≥ 2 := by exact Nat.Prime.two_le hp1
    have : p2 ≥ 3 := by linarith
    have : p3 ≥ 331 := by rw [hp]; nlinarith
    -- Use these bounds to show n is at least 1986
    rw [hn]
    nlinarith
