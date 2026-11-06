import Mathlib

/- The first term of an arithmetic sequence is $a_{1}=3$, and its common difference is 9. Prove that for every natural number $k$, the sequence contains the term $3 \cdot 4^{k}$.

---

Translate the above text into English, please retain the original text's line breaks and format, and output the translation result directly. -/
theorem algebra_219403 (a : ℕ → ℕ) (ha : ∀ n, a n = 3 + 9 * n) :
    ∀ k, ∃ n, a n = 3 * 4 ^ k := by
  -- simple induction on k
  intro k; induction k with
  | zero => use 0; rw [ha]; simp
  | succ k ih =>
    rcases ih with ⟨n, hn⟩
    use n + 4^k
    calc
      a (n + 4 ^ k) = 3 + 9 * n + 9 * 4^k := by rw [ha]; ring
      _ = 3 * 4^k + 9 * 4^k := by rw [←ha n, hn]
      _ = 3 * 4^(k + 1) := by ring