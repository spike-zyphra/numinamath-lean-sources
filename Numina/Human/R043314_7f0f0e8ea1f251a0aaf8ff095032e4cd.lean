import Mathlib

/- The sequence $y_{0}=1, y_{n+1}=\frac{1}{2}\left(3 y_{n}+\right.$
$\left.\sqrt{5 y_{n}^{2}-4}\right) \quad(n \geqslant 0)$ is a sequence of integers. -/

theorem number_theory_321068 (y : ℕ → ℝ)
    (h₀ : y 0 = 1)
    (h₁ : ∀ n, y (n + 1) = (3 * y n + Real.sqrt (5 * (y n) ^ 2 - 4)) / 2) :
    ∀ n, ∃ m : ℤ, y n = m := by

    -- we need to show that the expression in the square root is non-negative
    have u: ∀ n, 1 ≤ y n := by
      intro n
      induction' n with n ih
      . -- base case: n = 0
        simp [h₀]
      .
        specialize h₁ n
        rw [h₁]
        clear h₁
        have o: 1 ≤ √(5 * (y n) ^ 2 - 4) := by
          apply Real.le_sqrt_of_sq_le
          nlinarith
        nlinarith

    -- then we can show the key lemma to simplify the sequence
    have f: ∀ n, 1 ≤ n → y (n + 1) = y (n - 1) ∨ y (n + 1) = 3 * y n - y (n - 1) := by
      intro n hn
      have g1:= h₁ n
      have g2:= h₁ (n - 1)
      clear h₁
      rw [show n - 1 + 1 = n by omega] at g2
      replace g1: 2 * y (n + 1) - 3 * y n = Real.sqrt (5 * (y n) ^ 2 - 4) := by
        nlinarith
      replace g2: 2 * y n - 3 * y (n - 1) = Real.sqrt (5 * (y (n - 1)) ^ 2 - 4) := by
        nlinarith
      replace g1: (2 * y (n + 1) - 3 * y n) ^ 2 = Real.sqrt (5 * (y n) ^ 2 - 4) ^ 2 := by
        rw [g1]
      replace g2: (2 * y n - 3 * y (n - 1)) ^ 2 = Real.sqrt (5 * (y (n - 1)) ^ 2 - 4) ^ 2 := by
        rw [g2]
      have eq1: Real.sqrt (5 * (y n) ^ 2 - 4) ^ 2 = 5 * (y n) ^ 2 - 4 := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        specialize u n
        nlinarith
        apply Real.sqrt_nonneg
      have eq2: Real.sqrt (5 * (y (n - 1)) ^ 2 - 4) ^ 2 = 5 * (y (n - 1)) ^ 2 - 4 := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        specialize u (n - 1)
        nlinarith
        apply Real.sqrt_nonneg
      rw [eq1] at g1
      rw [eq2] at g2
      clear eq1 eq2
      -- then we use g1 - g2
      have g: (2 * y (n + 1) - 3 * y n) ^ 2 - 5 * y n ^ 2 - 4 -
      ((2 * y n - 3 * y (n - 1)) ^ 2 - 5 * y (n - 1) ^ 2 - 4) = 0 := by nlinarith
      have eq: (2 * y (n + 1) - 3 * y n) ^ 2 - 5 * y n ^ 2 - 4 -
      ((2 * y n - 3 * y (n - 1)) ^ 2 - 5 * y (n - 1) ^ 2 - 4)
      = 4 * (y (n + 1) - y (n - 1)) * (y (n + 1) - 3 * y n + y (n - 1)) := by  -- factor left hand side
        ring
      rw [eq] at g
      clear eq
      simp at g
      rcases g with g | g
      .
        left
        linarith
      .
        right
        linarith

    -- then we use the lemma to prove the original statement by induction
    intro n
    induction' n using Nat.strongRecOn with n ih
    by_cases l: n = 0
    . -- base case: n = 0
      simp [l]
      use 1
      simp [h₀]
    . -- case 1 ≤ n
      by_cases r: n = 1
      . -- case n = 1
        simp [r]
        specialize h₁ 0
        rw [show 1 + 0 = 1 by rfl] at h₁
        simp [h₀] at h₁
        norm_num at h₁
        use 2
        simp [h₁]
      . -- case n > 1
        replace l: 1 ≤ n - 1 := by omega
        clear r
        specialize f (n - 1) l
        rw [show n - 1 + 1 = n by omega] at f
        rcases f with f | f
        .
          rw [f]
          rw [show n - 1 - 1 = n - 2 by omega]
          specialize ih (n - 2)
          have o: n - 2 < n := by omega
          simp [o] at ih
          exact ih
        .
          rw [f]
          rw [show n - 1 - 1 = n - 2 by omega]
          have g1:= ih (n - 1)
          have g2:= ih (n - 2)
          clear ih h₁
          have o1: n - 1 < n := by omega
          simp [o1] at g1
          have o2: n - 2 < n := by omega
          simp [o2] at g2
          clear o1 o2
          obtain ⟨p, hp⟩ := g1
          obtain ⟨q, hq⟩ := g2
          use (3 * p - q)
          simp [hp, hq]