import Mathlib

/- Let $M$ be an odd natural number. Let $n$ be a natural number satisfying the following conditions:
1. $n$ is between 10 and 99, inclusive (i.e., $10 \le n \le 99$).
2. $n$ is divisible by $5$.
3. $n$ is not divisible by $3$.
4. $n$ is not divisible by $4$.
5. The product $M \cdot n$ is an even number.
6. The integer part of $n/10$ is greater than or equal to 6 (i.e., $6 \le \lfloor n/10 \rfloor$).
Show that $n=70$. -/
theorem number_theory_635247 (M : ℕ) (hM : Odd M) (n : ℕ) (hn : n ∈ Finset.Icc 10 99) (h₁ : 5 ∣ n) (h₂ : ¬3 ∣ n) (h₃ : ¬4 ∣ n) (h₄ : Even (M * n)) (h₅ : 6 ≤ n / 10) :
    n = 70 := by
  -- We first show that n is even.
  simp only [Nat.even_mul, show ¬Even M from Nat.not_even_iff_odd.mpr hM, false_or] at h₄
  -- We quantify over all possible values of n.
  revert n
  -- We check all possible values of n.
  native_decide
