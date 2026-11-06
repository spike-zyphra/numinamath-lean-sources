import Mathlib

/- The Fibonacci sequence is defined as follows: $F_{0}=0, F_{1}=1$, and $F_{n}=F_{n-1}+F_{n-2}$ for all integers $n \geq 2$. Find the smallest positive integer $m$ such that $F_{m} \equiv 0(\bmod 127)$ and $F_{m+1} \equiv 1(\bmod 127)$. -/
theorem number_theory_609646 :
    IsLeast {m | 0 < m ∧ Nat.fib m ≡ 0 [MOD 127] ∧ Nat.fib (m + 1) ≡ 1 [MOD 127]} 256 := by
  constructor
  . -- Let's compute fib 256 and fib 257
    norm_num
    -- Calculate their values modulo 127
    decide
  . -- We show that 256 is the smallest such number
    intro m ⟨h₁, h₂, h₃⟩
    -- We can prove that any m < 256 is not a solution by brute force
    by_contra! h₄
    revert h₁ h₂ h₃
    revert m
    native_decide
