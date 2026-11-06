import Mathlib

theorem AIME_Number_Theory_95085 (m:Int) (n:Nat) (r:Real) (npos:0<n) (rpos:0<r) (hr:r<1/1000)(hmn:m=(n+r)^3):(19≤n)∧(∃(m:Int) (r:Real),0<r∧r<1/1000 ∧ m=(19+r)^3):=by

--We prove that such n must be no less than 19, and for n=19, there are such n, then since 19 is the minimal for n, it gives the minimal m.
  constructor
  swap
--We prove that n=19 satisfies the property.
  · use 19^3+1, ((19:Real)^(3:Real)+1)^((1:Real)/3)-19
    split_ands
    · rw[sub_pos,one_div,Real.lt_rpow_inv_iff_of_pos]
      norm_num;norm_num;norm_num;norm_num
    · rw[sub_lt_iff_lt_add,one_div,Real.rpow_inv_lt_iff_of_pos]
      norm_num;norm_num;norm_num;norm_num
    · rw[one_div,←Real.rpow_natCast]
      norm_num
      simp only [one_div, Nat.ofNat_nonneg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,Real.rpow_inv_rpow]
--We prove that such m exists implies n>18.
  · -- Prove 19 ≤ n by contradiction
    by_contra h
    push_neg at h
--Now we assume n < 19, which would give us a contradiction.
--Since n < 19, n \leq 18.
    have h1 : (n : ℝ) ≤ (18 : ℝ) := by
      have hn : n ≤ 18 := by linarith
      exact_mod_cast hn
--We bound $n$ from above by 18, now we need to show for all $n \leq 18$ and $0 < r < 1/1000$, we have $m < n^3 + 1$ which contradicts $m = (n + r)^3$.
    have h2 : (n + (r : ℝ)) ^ 3 < ((n : ℝ) : ℝ) ^ 3 + 1 := by
--This inequality is crucial, we have to show that adding a small number and cubing only gives a bounded increase.
      have h3 : (r : ℝ) < 1 / 1000 := by linarith
      have h4 : (n : ℝ) ≤ (18 : ℝ) := h1
      nlinarith [sq_nonneg ((r : ℝ)), sq_nonneg ((n : ℝ)), sq_nonneg ((n + (r : ℝ)) : ℝ),
        sq_nonneg ((n + (1 / 1000 : ℝ)) : ℝ), sq_nonneg ((n : ℝ) - 18), sq_nonneg ((n : ℝ) - 19),
        sq_nonneg ((r : ℝ) - 0), sq_nonneg ((r : ℝ) - 1 / 1000)]
--We anayze the inequality by analyzing the derivatives of the cubing function, and confirm that the growth is less than 1 for $n \leq 18$.
--Now we have the real number inequality $(n + r)^3 < n^3 + 1$.
--We need that and the fact that $m = (n + r)^3$ to derive that $m < n^3 + 1$, which is a problem because $m$ is integer larger than $n^3$.
--Convert inequality to integer inequality:
    have h3 : (m : ℝ) < ((n : ℝ) : ℝ) ^ 3 + 1 := by
      have h4 : (m : ℝ) = (n + (r : ℝ)) ^ 3 := by
        exact_mod_cast hmn
      linarith [h4, h2]
    have h4 : m < (n ^ 3 + 1 : ℤ) := by
      have h6 : (m : ℝ) < (n ^ 3 + 1 : ℝ) := by
        exact_mod_cast h3
      have h7 : m < (n ^ 3 + 1 : ℤ) := by
        exact_mod_cast h6
      linarith
--From the inequality of real numbers, we've now converted it to integer inequality $m < n^3 + 1$
--We also need $m > n^3$, since $r > 0$
    have h8 : m > (n ^ 3 : ℤ) := by
      have h10 : (m : ℝ) > (n ^ 3 : ℝ) := by
        have h11 : (n + (r : ℝ)) ^ 3 > (n : ℝ) ^ 3 := by
          apply pow_lt_pow_left
          · -- Show (n + r) > (n) using the fact that r > 0
            linarith
          · -- Show 0 < (n + r) using n > 0 and r > 0
            linarith [show 0 < (n : ℝ) by exact_mod_cast show 0 < (n : ℕ) by linarith, show 0 < (r : ℝ) by linarith]
          all_goals nlinarith
        have h12 : (m : ℝ) = (n + (r : ℝ)) ^ 3 := by exact_mod_cast hmn
        have h13 : (n ^ 3 : ℝ) = (n : ℝ) ^ 3 := by norm_num
        linarith [h12, h11, h13]
      have h14 : m > (n ^ 3 : ℤ) := by
        exact_mod_cast h10
      linarith
--This leads to a contradiction because $m < n^3 + 1$ and $m > n^3$ is impossible for integer $m$.
    have h8' : m ≤ (n ^ 3 : ℤ) := by omega
    linarith