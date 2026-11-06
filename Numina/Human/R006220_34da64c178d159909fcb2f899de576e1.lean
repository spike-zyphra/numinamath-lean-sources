import Mathlib

/- Lemma 1: If $n$ is odd and divisible by 5, then the last digit of $n$ is 5. -/
lemma lemma_1 {n : ℕ} (h₁ : Odd n) (h₂ : 5 ∣ n) : n % 10 = 5 := by
  simp only [Odd] at h₁
  -- `omega` can solve this problem.
  omega

/- Lemma 2: A product of odd numbers is odd. -/
lemma lemma_2 {α : Type*} {s : Finset α} [DecidableEq α] {f : α → ℕ} (h : ∀ x ∈ s, Odd (f x)) : Odd (∏ x ∈ s, f x) := by
  -- We use induction on the finset.
  induction s using Finset.induction_on with
  | empty =>
    -- For empty finset, the product is 1, which is odd.
    simp
  | @insert x s hx ih =>
    -- For non-empty finset `insert x s` where `x ∉ s`, we simplify with the induction hypothesis.
    simp only [hx, not_false_eq_true, Finset.prod_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at h
    rcases h with ⟨h₁, h₂⟩
    -- The conclusion follows from the fact that the product of two odd numbers is odd.
    exact Odd.mul h₁ (ih h₂)

/- Let $a$ and $b$ be non-negative integers such that $a \le b$. Suppose there exists a non-negative integer $k$ such that the number $x = 10k+5$ satisfies $a \le x \le b$. Let $P$ be the product of all odd natural numbers $i$ in the interval $[a, b]$ (inclusive). Show that the last digit of $P$ is 5. -/
theorem number_theory_634787 {a b : ℕ} (hab : a ≤ b) (hk : ∃ k, a ≤ 10 * k + 5 ∧ 10 * k + 5 ≤ b) : (∏ i ∈ (Finset.Icc a b).filter Odd, i) % 10 = 5 := by
  -- We apply lemma 1. Now we need to show that the product is odd and divisible by 5.
  apply lemma_1
  -- We show that the product is odd.
  . -- It suffices to show that the factors are odd.
    refine lemma_2 fun x hx => ?_
    -- Since we only pick odd numbers, the condition is satisfied.
    exact (Finset.mem_filter.mp hx).2
  -- We show that the product is divisible by 5.
  . -- We pick some k such that 10k + 5 is in the interval.
    obtain ⟨k, hk⟩ := hk
    -- We show that 10k + 5 is an odd number in the interval.
    replace hk : 10 * k + 5 ∈ (Finset.Icc a b).filter Odd := by
      simp only [Finset.mem_filter, Finset.mem_Icc, hk, and_self, true_and]
      -- Since 10k + 5 = 2(5k + 2) + 1, it is odd.
      use 5 * k + 2
      ring
    -- So 10k + 5 is a factor of the product P.
    apply Finset.dvd_prod_of_mem (f := (·)) at hk
    -- We show that 5 ∣ 10k + 5 ∣ P.
    refine dvd_trans ?_ hk
    use 2 * k + 1
    ring