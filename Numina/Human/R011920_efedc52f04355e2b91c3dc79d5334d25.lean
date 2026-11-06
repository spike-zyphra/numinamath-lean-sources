import Mathlib

/- Let's define a property `K` for a sequence `a` and a natural number `k` as follows:
For all `n ≥ k`, `a (n + 5) = a (n + 4) + a n`. -/
def K (a : ℕ → ℕ) (k : ℕ) : Prop :=
    ∀ n ≥ k, a (n + 5) = a (n + 4) + a n

/- Uniqueness lemma: if two sequences `a` and `b` satisfy the property `K` for some `k`, and they are equal at `k`, `k + 1`, `k + 2`, `k + 3`, and `k + 4`, then they are equal for all `n ≥ k`. -/
def lemma_1 {a b : ℕ → ℕ} (k : ℕ) (ha : K a k) (hb : K b k) (heq : a k = b k ∧ a (k + 1) = b (k + 1) ∧ a (k + 2) = b (k + 2) ∧ a (k + 3) = b (k + 3) ∧ a (k + 4) = b (k + 4)) :
    ∀ n ≥ k, a n = b n := by
  intro n hn
  -- We want to use induction of 5 steps.
  -- So we generalize the goal to a conjunction of 5 equalities.
  suffices a n = b n ∧ a (n + 1) = b (n + 1) ∧ a (n + 2) = b (n + 2) ∧ a (n + 3) = b (n + 3) ∧ a (n + 4) = b (n + 4) from this.1
  -- We use induction on `n`.
  induction n, hn using Nat.le_induction with
  | base => exact heq
  | succ n hn ih =>
    -- We use the induction hypothesis to get the equality at `n + 5`.
    rcases ih with ⟨h₀, h₁, h₂, h₃, h₄⟩
    refine ⟨h₁, h₂, h₃, h₄, ?_⟩
    rw [ha n hn, hb n hn, h₀, h₄]

/- Define sequence $(a_{n})_{n=1}^{\infty}$ by $a_1=a_2=a_3=1$ and $a_{n+3}=a_{n+1}+a_{n}$ for all $n \geq 1$. Also, define sequence $(b_{n})_{n=1}^{\infty}$ by $b_1=b_2=b_3=b_4=b_5=1$ and $b_{n+5}=b_{n+4}+b_{n}$ for all $n \geq 1$. Prove that $\exists N \in \mathbb{N}$ such that $a_n = b_{n+1} + b_{n-8}$ for all $n \geq N$. -/
theorem number_theory_p64597 {a b : ℕ → ℕ} (ha₁ : a 1 = 1) (ha₂ : a 2 = 1) (ha₃ : a 3 = 1) (ha : ∀ n ≥ 1, a (n + 3) = a (n + 1) + a n) (hb₁ : b 1 = 1) (hb₂ : b 2 = 1) (hb₃ : b 3 = 1) (hb₄ : b 4 = 1) (hb₅ : b 5 = 1) (hb : ∀ n ≥ 1, b (n + 5) = b (n + 4) + b n) :
    ∃ N, ∀ n ≥ N, a n = b (n + 1) + b (n - 8) := by
  -- Setting `N = 9` is a good choice.
  use 9
  -- We prove that `a` and `n ↦ b (n + 1) + b (n - 8)` satisfy the property `K` for `k := 9`.
  have Ha : K a 9 := by
    -- We use the recurrence relation of `a`.
    intro n hn
    rw [ha (n + 2) (by simp), ha (n + 1) (by simp), ha n (by omega)]
    ring
  have Hb : K (fun n => b (n + 1) + b (n - 8)) 9 := by
    -- Since `b` has property `K` for `k = 1`, this proposition is obvious.
    intro n hn
    simp
    rw [hb (n + 1) (by simp), show n - 3 = n - 8 + 5 by omega, hb (n - 8) (by omega), show n - 8 + 4 = n - 4 by omega]
    ring
  -- Now we only need to prove that `a` and `b` are equal at `9`, `10`, `11`, `12`, and `13`.
  refine lemma_1 9 Ha Hb ?_
  -- We use the recurrence relation repeatedly with the initial values to compute the values.
  simp [ha, ha₁, ha₂, ha₃, hb, hb₁, hb₂, hb₃, hb₄, hb₅]
