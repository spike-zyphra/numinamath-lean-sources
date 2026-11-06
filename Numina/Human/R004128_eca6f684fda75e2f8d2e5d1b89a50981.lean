import Mathlib

/- Let $x_{1}=1$ and $x_{n+1}=x_{n}+\left\lfloor\frac{x_{n}}{n}\right\rfloor+2$ for $n=1,2,3, \ldots$, where $\lfloor x\rfloor$ denotes the largest integer not greater than $x$. Determine $x_{1997}$. -/
theorem number_theory_238792 (x : ℕ → ℤ)
    (hx1 : x 1 = 1)
    (hxn : ∀ n ≥ 1, x (n + 1) = x n + ⌊(x n / n : ℝ)⌋ + 2) :
    x 1997 = 23913 := by
  -- note that if xn = an+b with 0 ≤ b < n,
  -- then x_{n+1} = a(n+1) + b + 2
  have xsucc{n:ℕ}{a b: ℤ}(hn: n ≥ 1)(hb: 0 ≤ b ∧ b < n)
    (hxn': x n = a*n+b):
    x (n+1) = a * (n+1) + b + 2 := by
    have nnz: n ≠ 0 := by omega
    rw [hxn n hn, hxn']
    push_cast; rify at nnz
    rw [add_div, mul_add, mul_one]
    -- by our convention, b < n, so b/n < 1. floor of a + b/n is a.
    have: ⌊(a:ℝ)*n/n + b/n⌋ = a := by
      simp only [isUnit_iff_ne_zero, ne_eq, nnz,
      not_false_eq_true, IsUnit.mul_div_cancel_right,
      Int.floor_int_add, add_right_eq_self,
      Int.floor_eq_zero_iff, Set.mem_Ico]
      rify at hb
      constructor
      · apply div_nonneg hb.left (by simp)
      · rw [div_lt_one_iff]; left
        refine ⟨?_, hb.right⟩
        norm_cast
    rw [this]
    ring
  -- use induction, we can prove x (n+m) = a (n+m) + 2m
  have hxnm{n m:ℕ}{a:ℤ}(hn: n ≥ 1)(hm: m ≤ n)(hxn': x n = a*n):
    x (n+m) = a * (n+m) + 2*m := by
    induction' m with m ih
    · simp only [add_zero, hxn', CharP.cast_eq_zero, mul_zero]
    · push_cast
      simp only [← add_assoc]
      -- it suffices to find relations between x (n+m+1) and x(n+m)
      -- and it is from xsucc we prove before.
      have: (0:ℤ) ≤ 2*m ∧ 2*m < (n:ℤ)+m := by
        simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left,
        Nat.cast_nonneg, true_and]
        norm_cast
        linarith [hm]
      -- combine inductive hypothesis and xsucc.
      have mlen: m ≤ n := Nat.le_of_succ_le hm
      rw [xsucc (by linarith [hn]) this (ih mlen)]
      push_cast; ring
  -- hence we can prove if xn = an, then x_{2n} = (a+1)2n
  have hx2n{n:ℕ}{a:ℤ}(hn: n ≥ 1)(hxn': x n = a*n):
    x (2*n) = (a+1)*(2*n) := by
    -- take m=n at hxnm, done.
    nth_rw 1 [two_mul, hxnm hn le_rfl hxn']
    ring
  -- from hx2n use induction, we can decide 2^n
  have hx2pow{n:ℕ}(hn: n ≥ 1): x (2^n) = (n+1) * (2^n) := by
    -- by hxn, x2 = 4
    have hx2: x 2 = 4 := by
      rw [hxn 1 le_rfl, hx1]
      norm_num
    induction' n,hn using Nat.le_induction with n hn ih
    · simp [hx2]
    · push_cast
      have hn': 1 ≤ 2^n := Nat.one_le_pow _ _ (by norm_num)
      replace ih: x (2^n) = (n + 1) * ↑(2^n: ℕ) := by
        rw [ih]; norm_cast
      rw [pow_succ', hx2n hn' ih, pow_succ']
      norm_cast
  -- notice that 1024 = 2^10, and therefore x1024 = 11 x 1024
  have x1024: x 1024 = 11 * 1024 := by
    have: 1024 = 2^10 := by norm_num
    rw [this, hx2pow (by norm_num)]
    norm_num
  -- 1997 = 1024 + 973, so x1997 has the form x_{n+m}
  -- use x (n+m) = a (n+m) + 2m, done.
  have: 1997 = 1024 + 973 := by norm_num
  rw [this, hxnm (by norm_num) (by norm_num) x1024]
  -- 11×(1024+973) + 2×973 = 11×1997 + 1946 = 21967 + 1946 = 23913.
  norm_num