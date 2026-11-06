import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

/- 5. Let the sequence $\left(a_{n}\right)_{n \geqslant 1}$ be defined by $a_{1}=3, a_{2}=11$ and $a_{n}=4 a_{n-1}-a_{n-2}$, for $n \geqslant 3$. Prove that every term of this sequence is of the form $a^{2}+2 b^{2}$ for some natural numbers $a$ and $b$.

(Đorđe Baralić) -/
theorem algebra_103398 {a : ℕ → ℚ} (ha0 : a 0 = 1)
    (ha1 : a 1 = 3) (ha2 : a 2 = 11)
    (han : ∀ n, a (n + 2) = 4 * a (n + 1) - a n) :
    ∀ n ≥ 1, ∃ a' b, a n = a' ^ 2 + 2 * b ^ 2 := by
  have odd_even : ∀ n ≥ 1, a (2*n - 1) = (a (n - 1))^2 + 2 * ((a n - a (n - 1)) / 2)^2 ∧ a (2*n) = (a n)^2 + 2 * ((a n - a (n - 1)) / 2)^2 := by
    intro n hn
    -- Use induction
    induction n, hn using Nat.le_induction with
    -- Check base case
    | base => simp; rw [ha0, ha1]; norm_num; tauto
    -- Induction step
    | succ n hn ih =>
      -- Prove the desired for 2*n + 1
      -- Write a (n - 1) in terms of the next terms
      have recursion_backward : a (n - 1) = 4*(a n) - a (n + 1) := by
        rw [show n + 1 = (n - 1) + 2 by simp; exact symm (Nat.sub_add_cancel hn)]
        nth_rw 2 [show n = (n - 1) + 1 by exact symm (Nat.sub_add_cancel hn)]
        linarith [han (n - 1)]
      have left_case : a (2*n + 1) = (a n)^2 + 2 * ((a (n + 1) - a n) / 2)^2 := by
        have : 2*n + 1 = (2*n - 1) + 2 := by simp; rw [Nat.sub_add_cancel (by linarith)]
        rw [this, han (2*n - 1), Nat.sub_add_cancel (by linarith), ih.1, ih.2]
        -- Introduce an intermediary computation
        trans 11/2 * (a n)^2 - 3*(a n)*(a (n - 1)) + 1/2 * (a (n - 1))^2
        · ring
        -- Use the recursion
        rw [recursion_backward]
        -- Now just computation
        ring
      constructor
      · -- This is precisely the statement of left_case
        tauto
      -- Use previous induction steps
      rw [mul_add, mul_one, han (2*n), left_case, ih.2, Nat.add_sub_cancel, recursion_backward]
      -- Reduce to computation
      ring
  intro n hn
  have n_even_odd : Odd n ∨ Even n := Or.symm (Nat.even_or_odd n)
  -- Break into cases of whether n is odd or even
  rcases n_even_odd with n_odd | n_even
  · -- Odd case
    rcases n_odd with ⟨k, hk⟩
    rw [show 2*k + 1 = 2*(k + 1) - 1 by rw [mul_add]; simp] at hk
    use a k
    use (a (k + 1) - a k) / 2
    rw [hk]
    exact (odd_even (k + 1) (by linarith)).1
  -- Even case
  rcases n_even with ⟨k, hk⟩
  use a k
  use (a k - a (k - 1)) / 2
  rw [show k + k = 2*k by rw [two_mul]] at hk
  rw [hk]
  exact (odd_even k (by linarith)).2