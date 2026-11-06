import Mathlib

/- 2. Prove that $10^{n}+1$ is divisible by 11 for any odd natural value of $n$. -/
theorem number_theory_188680 (n : ℕ) (h : Odd n) : 11 ∣ 10^n + 1 := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero =>
    simp
  | succ k ih =>
    norm_num [pow_succ, pow_mul] at ih ⊢
    set x := 100 ^ k
    omega
