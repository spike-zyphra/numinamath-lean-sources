import Mathlib
open Real
/- 5. Given a sequence of numbers $a_{1}, a_{2}, \cdots, a_{100}$, where $a_{3} = 9, a_{7} = -7, a_{98} = -1$, and the sum of any three consecutive numbers is a constant. Then the value of $a_{1} + a_{2} + \cdots + a_{100}$ is ( ).
(A) 0
(B) 40
(C) 32
(D) 26 -/
theorem algebra_326172 {a : ℕ → ℝ} (h : ∃ c, ∀ n, a n + a (n + 1) + a (n + 2) = c) (ha1 : a 2 = 9) (ha2 : a 6 = -7) (ha3 : a 97 = -1) : ∑ i in Finset.range 100, a i = 26:= by
  -- Extract the constant c from the hypothesis
  rcases h with ⟨c, h⟩

  -- Prove that terms with indices differing by multiples of 3 are equal
  -- i.e., a(t+3k) = a(t) for any t and k
  have h1 : ∀ t k : ℕ, a (3 * k + t) = a t:= by
    intro t k
    induction k with
    | zero =>
      -- Base case: k = 0
      simp
    | succ k ih =>
      -- Inductive step: assume true for k, prove for k+1
      rw [show 3 * (k + 1) + t = 3 * k + t + 3 by ring]
      -- Apply the constant sum property at position 3*k+t
      have g1:= h (3 * k + t)
      -- Apply the constant sum property at position 3*k+t+1
      have g2:= h (3 * k + t + 1)
      rw [show 3 * k + t + 1 + 1 = 3 * k + t + 2 by ring] at g2
      rw [show 3 * k + t + 2 + 1 = 3 * k + t + 3 by ring] at g2
      -- Use linear arithmetic to complete the proof
      linarith

  -- Specialize h1 for different remainders modulo 3
  have h2:= h1 1
  have h3:= h1 2
  replace h1:= h1 0
  simp at h1

  -- Use the given value a₇ = -7 to determine a₁
  have g1:= h1 2
  simp at g1
  rw [ha2] at g1
  rw [←g1] at h1

  -- Use the given value a₃ = 9 to determine a₃
  rw [ha1] at h3

  -- Use the given value a₉₇ = -1 to determine a₁
  have g2:= h2 32
  simp at g2
  rw [ha3] at g2
  rw [←g2] at h2
  clear g2

  -- Prove that the sum of the first 3k+1 terms equals k-7
  have h4 : ∀ k : ℕ, ∑ i ∈ Finset.range (3 * k + 1), a i = k - 7:= by
    intro k
    induction k with
    | zero =>
      -- Base case: k = 0
      simp
      linarith
    | succ k ih =>
      -- Inductive step: assume true for k, prove for k+1
      rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 1 + 1 + 1 by ring]
      -- Split the sum by adding three more terms
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      -- Use the induction hypothesis
      rw [ih]
      -- Apply the pattern of terms with indices differing by multiples of 3
      rw [h2 k, h3 k]
      rw [show 3 * k + 3 = 3 * (k + 1) by ring]
      rw [h1 (k + 1)]
      simp
      linarith

  -- Apply the formula for k = 33 to get the sum of the first 100 terms
  specialize h4 33
  rw [show 3 * 33 + 1 = 100 by ring] at h4
  rw [h4]
  simp
  linarith
