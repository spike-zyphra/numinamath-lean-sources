import Mathlib

/- 2. Let $f(n)$ be a function defined on the set of natural numbers and taking values in the set of natural numbers. Prove that if for each value of $n$, the inequality $f(n+1)>f[f(n)]$ holds, then for every value of $n$, $f(n)=n$.
 -/
theorem number_theory_292888 (f : ℕ → ℕ) (h : ∀ n, f (n + 1) > f (f n)) : ∀ n, f n = n := by
  -- we prove for naturals with 0instead of positive numbers as both are provable in same way
  -- first we prove by induction that k ≤ n implies k ≤ f(n)
  have h₁ (k : ℕ): (n : ℕ) → (k ≤ n) → k ≤ f n := by
    induction' k with k ih
    . simp
      -- in inductive step to prove k + 1 ≤ n imples k+1 ≤ f(n)
      -- first note k ≤ f (n-1) as k ≤ n - 1
    . rintro n hkn
      have : k ≤ f (n - 1) := by
        apply ih
        omega
      -- next note that k ≤ f (f(n-1)) < f (n) so k + 1 ≤ f (n)
      have : k < f n := by calc
        k ≤ f (f (n - 1)) := by
          apply ih
          exact this
        _ < f (n-1 + 1) := by apply h
        _ = f n := by congr; omega
      omega
  -- last fact easily proves n ≤ f(n)
  have h₂ (n : ℕ) : n ≤ f n := by exact h₁ n n (by rfl)
  -- also easily proved f(n) ≤ f(f(n)) < f(n + 1), but this means f is strictly monotonous
  have h₃ (n : ℕ) : f n < f (n + 1) := by calc
    f n ≤ f (f n) := h₂ (f n)
    _ < f (n + 1) := h n
  replace h₃ : StrictMono f := by exact strictMono_nat_of_lt_succ h₃
  -- now we prove n = f(n) for some particular n
  rintro n
  -- n ≤ f(n) by h₂
  -- f(n) < n+1 by strictly monotonicity at f(f(n)) < f(n+1)
  have hn₁ : n ≤ f n := h₁ n n (by rfl)
  have hn₂ : f n < n + 1 := by exact (StrictMono.lt_iff_lt h₃).mp (h n)
  -- the two inequality imply f(n) = n
  omega