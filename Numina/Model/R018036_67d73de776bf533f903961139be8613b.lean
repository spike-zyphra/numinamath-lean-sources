import Mathlib

theorem number_theory_55895 (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (hmn : Nat.Coprime m n) (h : (m / n : ℝ) = (366 / 12 : ℝ)) :
    m + n = 63 := by

  have h1 : (m : ℝ) / (n : ℝ) = (366 : ℝ) / (12 : ℝ) := by
    linarith [h]

  have h2 : m * 12 = 366 * n := by
    have h3 : (m : ℝ) * (12 : ℝ) = (366 : ℝ) * (n : ℝ) := by
      field_simp [(show (n : ℝ) ≠ 0 by positivity), (show (12 : ℝ) ≠ 0 by norm_num)] at h1 ⊢
      nlinarith [h1]
    exact_mod_cast h3

  -- Simplifying $12 \cdot m = 366 \cdot n$ by dividing both sides by 6:
  -- $2 \cdot m = 61 \cdot n$
  have h4 : m * 2 = 61 * n := by
    omega

  have h5 : m = 61 := by
    -- Let's prove from $2 \cdot m = 61 \cdot n$ that $m = 61$ and $n = 2$ given they're coprime.
    -- From the equation $2 \cdot m = 61 \cdot n$, we see that $m$ must be a multiple of 61 (since 2 and 61 are coprime).
    have h6 : m * 2 = 61 * n := h4
    have h7 : m ∣ 61 * n := by
      use 2
      all_goals linarith

    -- Since $\text{gcd}(m, n) = 1$ and $m | a \cdot n$, then $m | a$
    have h8 : m ∣ 61 := by
      have h9 : m ∣ 61 * n := h7
      have h10 : Nat.Coprime m n := hmn
      have h11 : m ∣ 61 := by
        apply Nat.Coprime.dvd_of_dvd_mul_right h10 h9
      exact h11

    -- $m$ divides 61 and $m > 0$, $m$ must be 1, 61.
    have h12 : m = 1 ∨ m = 61 := by
      have h13 : m ∣ 61 := h8
      have h14 : m ≤ 61 := by
        exact Nat.le_of_dvd (by linarith) h13
      interval_cases m <;> try { tauto }

    -- Now we need to determine which of $m = 1$ or $m = 61$ is valid with the equation $2 \cdot m = 61 \cdot n$.
    rcases h12 with (h15 | h16)
    · -- Assume m = 1
      rw [h15] at h4
      omega -- To show contradiction
    · -- Assume m = 61
      exact h16

  -- Now that we have $m = 61$, we can find $n$ from the equation $2 \cdot m = 61 \cdot n$
  have h8 : n = 2 := by
    rw [h5] at h4
    linarith

  -- Now, $m = 61$ and $n = 2$, so $m + n = 63$.
  omega