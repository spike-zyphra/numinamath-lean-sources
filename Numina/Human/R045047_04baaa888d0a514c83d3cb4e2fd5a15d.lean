import Mathlib

/- 6-20 Let $f(n)$ be a function defined on the set of natural numbers, and the values it takes are also in the set of natural numbers. Prove: If for every natural number, $f(n+1) >$ $f[f(n)]$, then $f(n)=n$ for every $n$ value. -/
theorem inequalities_128869 (f : ℕ → ℕ) (h : ∀ n, f (n + 1) > f (f n)) (n : ℕ) : f n = n := by
  -- We first show that if m ≥ n, then f m ≥ n.
  have H₁ (n : ℕ) : ∀ m ≥ n, f m ≥ n := by
    -- We prove this by induction on n.
    induction n with
    -- The base case is trivial.
    | zero => simp
    | succ n ih =>
      -- If ∀ m ≥ n, f m ≥ n
      -- Now m ≥ n + 1
      -- So m - 1 ≥ n, and f (m - 1) ≥ n, so f (f (m - 1)) ≥ n
      -- Then f m = f (m - 1 + 1) > f (f (m - 1)) ≥ n
      intro m hm
      calc f m
        _ > f (f (m - 1)) := by simpa [show 1 ≤ m by omega] using h (m - 1)
        _ ≥ n := ih _ (ih _ (by omega))
  -- Set n and m to be f n, we get f (f n) ≥ f n.
  have H₂ (n : ℕ) : f (f n) ≥ f n := H₁ _ _ (by simp)
  -- f (n + 1) > f (f n) ≥ f n, so f (n + 1) > f n
  have H₃ (n : ℕ) : f n < f (n + 1) := Nat.lt_of_le_of_lt (H₂ n) (h n)
  -- So f is strictly increasing.
  apply strictMono_nat_of_lt_succ at H₃
  -- Since f (n + 1) > f (f n), we get n + 1 > f n.
  have H₄ (n : ℕ) : n + 1 > f n := H₃.lt_iff_lt.1 (h n)
  -- Also, f n ≥ n, so f n = n.
  exact Nat.eq_of_le_of_lt_succ (H₁ n n (by simp)) (H₄ n)
