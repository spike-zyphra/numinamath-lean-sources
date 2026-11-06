import Mathlib

/- 11.2. Let the sequence $\left(a_{n}\right)_{n=0}^{\infty}$ be such that $a_{1}=1$ and $a_{m+n}+a_{m-n}=\frac{1}{2}\left(a_{2 m}+a_{2 n}\right), \quad \forall m \geq n \geq 0$. Determine $a_{2020}$. -/

theorem algebra_167554 (a : ℕ → ℝ) (h1 : a 1 = 1) (h : ∀ m n, m ≥ n → a (m + n) + a (m - n)
    = (a (2 * m) + a (2 * n)) / 2) : a 2020 = 2020 ^ 2 := by

  -- First we show that a 0 = 0
  have h0 : a 0 = 0 := by
    have : a 0 + a 0 = (a 0 + a 0) / 2 := by rw [← h 0 0 (by linarith)]
    linarith

  -- We prove by induction that a n = n ^ 2
  have (n : ℕ) : a n = n ^ 2 := by
    induction' n using Nat.strong_induction_on with n hn
    rcases Nat.lt_trichotomy n 1 with hlt | heq | hgt
    · -- For n < 1, we have n = 0, and the result is trivial
      simp only [Nat.lt_one_iff] at hlt
      rw [hlt]
      simp [h0]
    · -- For n = 1, we have a 1 = 1, and the result is trivial
      rw [heq]
      simp [h1]
    · -- For n + 1, we derive a recurrence relation
      -- First we prove that a (2 * n) = 4 * a n
      have h_twice : ∀ n : ℕ, a (2 * n) = 4 * a n := by
        intro n
        have := h n 0 (by linarith)
        simp only [add_zero, tsub_zero, mul_zero, h0] at this
        linarith
      -- We compute a 2 explicitly
      have h2 : a 2 = 4 := by simp [h_twice 1, h1]
      -- We find a recurrence relation for a n
      have h_rec : ∀ n : ℕ, a (n + 2) = 2 * a (n + 1) - a n + 2:= by
        intro n
        have := h (n + 2) n (by linarith)
        rw [(by linarith : n + 2 + n = 2 * (n + 1)), (by simp : n + 2 - n = 2), h2] at this
        repeat rw [h_twice] at this
        linarith
      -- We use the recurrence relation to prove the result
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
      rw [add_comm 1, add_assoc, (by ring : 1 + 1 = 2)] at hk
      rw [hk, h_rec, hn (k + 1) (by linarith), hn k (by linarith)]
      rify
      ring

  exact this 2020