import Mathlib

/- Let $m$ be the product of all positive integers less than $4!$ which are invertible modulo $4!$. Find the remainder when $m$ is divided by $4!$.

(Here $n!$ denotes $1\times\cdots\times n$ for each positive integer $n$.) -/
theorem number_theory_15019 : (∏ i ∈ (Finset.Ico 1 24).filter (fun x => Nat.Coprime x 24), i) % 24 = 1 := by
  decide