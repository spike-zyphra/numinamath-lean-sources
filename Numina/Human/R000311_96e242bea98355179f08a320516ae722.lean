import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Suppose  $a$  is a complex number such that
\[a^2+a+\frac{1}{a}+\frac{1}{a^2}+1=0\]
If  $m$  is a positive integer, find the value of
\[a^{2m}+a^m+\frac{1}{a^m}+\frac{1}{a^{2m}}\]-/
theorem number_theory_8880
  (a : ℂ)
  (h₀ : a ≠ 0)
  (h₁ : a^2 + a + 1 / a + 1 / a^2 + 1 = 0) :
  ∀ m > 0, m % 5 = 0 → a^(2 * m) + a^m + 1 / a^m + 1 / a^(2 * m) = 4 ∧
  m % 5 ≠ 0 → a^(2 * m) + a^m + 1 / a^m + 1 / a^(2 * m) = -1 := by
    -- $a \ne 1$
    have ane1 : a ≠ 1 := by
      by_contra!
      simp [this] at h₁
      norm_cast at h₁
    -- we simply have  $a^{4}+a^{3}+a+1+a^2=0$  or  $a^{5}=1$
    -- (since  $a \neq 1$ ) so we have  $a$  is $5$ th root of unity.
    have h2 : a^5 = 1 := by
      have c1 : a^4 + a^3 + a^2 + a + 1 = 0 := by
        apply_fun (· * a^2) at h₁
        simp only [one_div, add_mul, ← pow_add, reduceAdd, one_mul, zero_mul] at h₁
        rw [←h₁]
        field_simp
        ring_nf
      have c2 : a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = (a^5 - 1) / (a - 1) := by
        rw [←geom_sum_eq ane1 5]
        simp [Finset.sum_range_succ]
        ring
      rw [c1] at c2
      have : a^5 - 1 = 0 := by
        have := div_eq_zero_iff.1 c2.symm
        rw [or_iff_left (by exact fun tmp => (by
          have : a = 1 := eq_of_sub_eq_zero tmp
          tauto))] at this
        exact this
      apply_fun (· + 1) at this
      norm_num at this
      exact this
    -- now we know that every power of  $5$ th root of unity repeats under
    -- $\pmod 5$  so we use this fact
    intro m _ hmmod
    have h3 : m % 5 < 5 := by refine mod_lt m (by simp)
    have aux : ∀ k, a^k = a^(k % 5) := by
      intro k
      exact pow_eq_pow_mod k h2
    rw [aux m, aux (2 * m)]
    have h4 : 2 * m % 5 < 5 := by refine mod_lt (2 * m) (by simp)
    -- discuss the value of $m % 5$ and $2 * m % 5$
    interval_cases m % 5 <;> (interval_cases 2 * m % 5 <;> tauto)
