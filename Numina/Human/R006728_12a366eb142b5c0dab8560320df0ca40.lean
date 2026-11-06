import Mathlib

/-909 Let $n$ be an integer greater than 2. Let $N_n$ be the integer $(n^2)^3 - ((n-2)^3)^2$.
Note that this expression can be simplified to $n^6 - (n-2)^6$.
Let $S_n$ denote the sum of all distinct prime factors of $N_n$.
Show that for $n=4$, the sum $S_n$ is equal to 12. -/

theorem number_theory_640595 (N S: ℕ → ℕ) (h1: ∀ n, 2 < n → N n = (n ^ 2) ^ 3 - ((n - 2) ^ 3) ^ 2)
  (h2: ∀ n, 2 < n → S n = ∑ x ∈ (Nat.primeFactors (N n)), x): n = 4 → S n = 12 := by

    intro h
    suffices N 4 = 4032 by
      specialize h2 4 (by omega)
      rw [h, h2, this]
      native_decide
    specialize h1 4 (by omega)
    simp [h1]
