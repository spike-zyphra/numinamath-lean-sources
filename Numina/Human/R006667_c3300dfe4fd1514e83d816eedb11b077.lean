import Mathlib

/-
Let $K$ be an integer. A three-digit number $n$ is an integer such that $100 \le n \le 999$. Let $a$ be its first digit and $c$ be its last digit. Assume $c \ne 0$. The number $n$ is $K$ times $c$. If $K=101$, show that $n$ divided by its first digit $a$ is $101$.
-/

theorem number_theory_639863 (K:ℕ) (hk: K = 101) (n:ℕ) (nl: 100 ≤ n) (nu: n ≤ 999) (a:ℕ) (c:ℕ) (ha: a = n/100) (hc : c = n%10) (cnne0: c ≠ 0) (hn: n = K * c):
(n:ℚ) / a = 101 := by
  
  --We will simple show that no matter the value of c is, we always have our claim.

  have ane0 : a ≠ 0 := by omega
  field_simp
  norm_cast

  have cu : c < 10 := by 
    have : 0 < 10 := by norm_num
    apply Nat.mod_lt at this
    have : n % 10 < 10 := by exact this
    rw [←hc] at this
    exact this
  have cl : 0 < c := by omega

  interval_cases c <;>
  simp [hk] at hn <;>
  simp [hn] at ha <;>
  simp [hn, ha]