import Mathlib

/- 11th Australian 1990 Problem A2 Show that there are infinitely many positive integers m, n such that m divides n 2 + 1 and n divides m 2 + 1. -/
theorem number_theory_137851 :
    ∀ N : ℕ, ∃ m n : ℕ, m > N ∧ n > N ∧ m ∣ n^2 + 1 ∧ n ∣ m^2 + 1 := by
  rintro N
  -- we'll prove F(2*(N+5) + 1) and F(2*(N+5) + 3) as such n, m which are larger than N
  use Nat.fib (2 * (N + 5) + 1), Nat.fib (2 * (N + 5) + 3)
  -- first a lemma that F(2*n + 5) = 3 * F(2*n + 3) - F(2*n + 1)
  have fib_lemma (n : ℕ) : Nat.fib (2 * n + 5) = 3 * Nat.fib (2 * n + 3) - Nat.fib (2 * n + 1) := by
    rw [Nat.fib_add_two,  Nat.fib_add_two (n := 2 * n + 2)]
    have := Nat.fib_add_two (n := 2 * n + 1)
    ring_nf at this ⊢
    omega
  -- now using the lemma we use induction to prove F(2*n+1) * F(2*n+5) = F(2*n+3)^2 + 1
  replace fib_lemma (n : ℕ) : Nat.fib (2 * n + 1) * Nat.fib (2 * n + 5) = Nat.fib (2 * n + 3) ^ 2 + 1 := by
    induction' n with m hm
    . rfl
    . calc
      _ = Nat.fib (2 * m + 3) * Nat.fib (2 * m + 7) := by ring_nf
      _ = Nat.fib (2 * m + 3) * (3 * Nat.fib (2 * m + 5) - Nat.fib (2 * m + 3)) := by
        -- use the previous lemma here
        have := fib_lemma (m + 1)
        ring_nf at this ⊢
        rw [this]
      _ = 3 * Nat.fib (2 * m + 5) * Nat.fib (2 * m + 3) - Nat.fib (2 * m + 3) ^ 2 := by
        rw [Nat.mul_sub]
        ring_nf
      _ = 3 * Nat.fib (2 * m + 5) * Nat.fib (2 * m + 3) - (Nat.fib (2 * m + 1) * Nat.fib (2 * m + 5) - 1) := by
        congr
        omega
      _ = 3 * Nat.fib (2 * m + 5) * Nat.fib (2 * m + 3) - Nat.fib (2 * m + 1) * Nat.fib (2 * m + 5) + 1 := by
        have : Nat.fib (2 * m + 1) * Nat.fib (2 * m + 5) ≤ 3 * Nat.fib (2 * m + 5) * Nat.fib (2 * m + 3) := by
          rw [show Nat.fib (2 * m + 1) * Nat.fib (2 * m + 5) = 1 * Nat.fib (2 * m + 5) * Nat.fib (2 * m + 1) by ring]
          gcongr
          . norm_num
          . apply Nat.fib_mono
            linarith
        simp at this
        omega
      _ = Nat.fib (2 * m + 5) * (3 * Nat.fib (2 * m + 3) - Nat.fib (2 * m + 1)) + 1 := by
        rw [Nat.mul_sub]
        ring_nf
      _ = Nat.fib (2 * m + 5) ^ 2 + 1 := by
        -- use the lemma again here.
        have := fib_lemma m
        ring_nf at this ⊢
        rw [← this]
        ring
      _ = Nat.fib (2 * (m + 1) + 3) ^ 2 + 1 := by
        ring_nf
  -- now we can prove the goals
  and_intros
  -- by n ≤ F(n) for 5 ≤ n, we can prove N ≤ n, m
  . have := Nat.le_fib_self (show 5 ≤ 2 * (N + 5) + 1 by linarith)
    linarith
  . have := Nat.le_fib_self (show 5 ≤ 2 * (N + 5) + 3 by linarith)
    linarith
  -- for the divisibility we use last lemma to show the divisibility
  . use Nat.fib (2 * (N+5) + 5)
    rw [fib_lemma]
  . rw [show 2 * (N + 5) + 1 = 2 * (N + 4) + 3 by ring, show 2 * (N + 5) + 3 = 2 * (N + 4) + 5 by ring]
    use Nat.fib (2 * (N + 4) + 1)
    rw [mul_comm (Nat.fib _), fib_lemma]