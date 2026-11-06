import Mathlib

def A (n : ℕ) : ℕ := (Nat.primeFactors n).sum id

-- Let $M$ be a positive integer and $S$ be a positive integer. We are looking for natural numbers $n$ such that $1 \le n \le M$ and $A(n) = S$.
-- Show that if $M=50$ and $S=7$, the set of such natural numbers $n$ is $\{7, 10, 20, 40, 49, 50\}$.
theorem number_theory_637613 {M S: ℕ} (hM : M = 50) (hS : S = 7) : (Finset.Icc 1 M).filter (fun n => A n = S) = {7, 10, 20, 40, 49, 50}:= by
  ext n
  simp
  constructor
  . intro ⟨⟨h1, h2⟩, h3⟩
    subst M S
    interval_cases n
    all_goals simp
    all_goals contrapose h3; native_decide
  . rw [hM, hS]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals native_decide
