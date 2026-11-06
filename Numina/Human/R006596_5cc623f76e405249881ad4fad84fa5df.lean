import Mathlib
open Nat

/-
Prove that for all natural numbers M ≥ 1,
the digit sum of the number n_w(M) = (10^(M+1) - 9M - 10)/9
is divisible by 9.
-/
theorem sum_mod_9_eq_0 (M : ℕ) (hM : 1 ≤ M)
    (n_w : ℕ → ℕ) (hn_w : n_w = fun (M : ℕ) ↦ (10^(M + 1) - 9 * M - 10) / 9) (digit_sum : ℕ → ℕ)
    (hdigit_sum0 : digit_sum 0 = 0)
    (hdigit_sum : ∀ n, digit_sum (n + 1) = ((n + 1) % 10) + digit_sum ((n + 1) / 10)) :
      digit_sum (n_w M) % 9 = 0 := by
  -- Key lemma: digit_sum n ≡ n mod 9
  have h_mod (n : ℕ) : digit_sum n % 9 = n % 9 := by
    refine Nat.strong_induction_on n ?_
    intro k ih
    cases k with
    | zero => simp [hdigit_sum0]
    | succ k₀ =>
      set d : ℕ := (k₀ + 1) % 10 with hd -- last digit
      set q : ℕ := (k₀ + 1) / 10 with hq -- remaining digits after removing last digit
      have hsplit : k₀ + 1 = d + 10 * q := by
        simpa [hd, hq] using (Nat.mod_add_div (k₀ + 1) 10).symm  -- number decomposition
      have hds : digit_sum (k₀ + 1) = d + digit_sum q := by
        rw [hdigit_sum, hd, hq]  -- digit sum definition
      calc
        digit_sum (k₀ + 1) % 9
          = (d + digit_sum q) % 9 := by rw [hds]
        _ = ((d % 9) + (digit_sum q % 9)) % 9 := by rw [Nat.add_mod]
        _ = ((d % 9) + (q % 9)) % 9 := by
          rw [ih q (Nat.div_lt_self (Nat.succ_pos _) (by decide))]
        _ = (d + 10 * q) % 9 := by
          rw [← Nat.add_mod]
          have hdq : d + 10 * q = d + q + 9 * q := by ring
          rw [hdq]
          norm_num
        _ = (k₀ + 1) % 9 := by
          rw [hsplit]
  -- Main induction on M
  induction M,hM using Nat.le_induction with
  | base => -- M = 1 case
    rw [hn_w]
    norm_num  --化简
    have : digit_sum 9 = 9 := by
      rw [hdigit_sum] -- 9 + digit_sum 0
      norm_num
      simp [hdigit_sum0]
    rw [this] --transfer back to d_s 9 % 9 = 0
  | succ k hk ih => -- M = k+1 case
    have h1 : n_w (k + 1) = 10 * n_w k + 9 * k + 9 :=
      calc
      n_w (k + 1) = (10 ^ (k + 2) - 9 * (k + 1) - 10) / 9 := by rw [hn_w]
      _ = (10 * 10 ^ (k + 1) - (9 * k + 9) - 10) / 9 := by ring_nf
      _ = (10 * 10 ^ (k + 1) - 9 * k - 9 - 10) / 9 := by
        have : 10 * 10 ^ (k + 1) - (9 * k + 9) - 10 = 10 * 10 ^ (k + 1) - 9 * k - 9 - 10 := by simp only [Nat.sub_sub, Nat.add_assoc]
        rw [this]
      _ = (10 * (10 ^ (k + 1) - 9 * k - 10) + 81 * k + 81) / 9 := by
        rcongr
        -- Prove that 10^(k+1) - 9k ≥ 10 for k ≥ 1
        have r:∀ k≥1,10 ^ (k + 1) - 9 * k ≥ 10:=by
          apply Nat.le_induction
          { -- k=1 case
            simp
          }
          { -- k=i+1 case
            intro i hi hbase
            have goal_expr : 10^((i + 1) + 1) - 9 * (i + 1) = 10 * 10^(i + 1) - 9 * i - 9 := by omega
            have ih_expr : 10^(i + 1) ≥ 10 + 9 * i := by omega
            calc
              10^((i + 1) + 1) - 9 * (i + 1) = 10 * 10^(i + 1) - 9 * i - 9 := by rw [goal_expr]
              _ ≥ 10 * (10 + 9 * i) - 9 * i - 9 := by gcongr
              _ = 100 + 90 * i - 9 * i - 9 := by ring_nf
              _ = 91 + 81 * i := by omega
              _ ≥ 10 := by linarith
          }
        have r':10 ^ (k + 1) - 9 * k ≥ 10:=by exact r k hk
        omega
      _ = 10 * n_w k + 9 * k + 9 := by
        refine Nat.div_eq_of_eq_mul_right (by trivial) ?_
        rw [hn_w]
        nth_rw 2 [add_assoc]
        rw [mul_add,mul_add,← add_assoc]
        nth_rw 2 [← mul_assoc]
        simp
        rw [← mul_assoc,mul_right_comm]
        set curr:=10 ^ (k + 1) - 9 * k - 10
        -- Prove (10^(k+1) - 9k - 10) is divisible by 9
        have heq1:∀ k≥1,(10 ^ (k + 1) - 9 * k - 10) % 9=0:=by
          apply Nat.le_induction
          {
            omega
          }
          {
            intro k hk hk'
            -- Expand 10^(i+2)
            rw [pow_add,mul_add,pow_one,mul_one]
            rw [show 10 ^ (k + 1) * 10 = 10 ^ (k + 2) by ring_nf]
            rw [show 9 * k + 9 = 9 * (k + 1) by ring]
            -- Define helper function A(n) = 10^(n+1) - 9n - 10
            set A : ℕ → ℕ := fun n ↦ 10^(n+1) - 9*n - 10 with hA
            -- Prove recurrence: A(i+1) = 10*A(i) + 81(i+1)
            have rel : A (k + 1) = 10 * A k + 81 * (k + 1) := by
              rw [hA]
              simp
              have:10 * (10 ^ (k + 1) - 9 * k - 10) + 81 * (k + 1)=10 ^ (k + 1 + 1) - 9 * (k + 1) - 10:=by
                calc
                  10 * (10^(k + 1) - 9 * k - 10) + 81 * (k + 1)
                  = 10 * 10^(k + 1) - 10 * (9 * k) - 10 * 10 + 81 * (k + 1) := by ring_nf;omega
                _ = 10^(k + 2) - 90 * k - 100 + 81 * k + 81 := by
                      rw [Nat.pow_succ, show k + 2 = (k + 1) + 1 by rfl, Nat.pow_succ]
                      ring_nf
                _ = 10^(k + 2) - 9 * k - 19 := by
                  -- Prove lower bound for algebraic manipulation
                  have helper:∀ k≥1,10 ^ (k + 2) - 90 * k≥100:=by
                    apply Nat.le_induction
                    {
                      simp
                    }
                    {
                      intro i hi hbase
                      have goal_expr : 10^((i + 1) + 2) - 90 * (i + 1) = 10 * 10^(i + 2) - 90 * i - 90 := by
                        rw [add_right_comm,pow_add,mul_add,mul_one]
                        simp
                        omega
                      have ih_expr : 10^(i + 2) ≥ 100 + 90 * i := by
                        omega
                      calc
                        10^((i + 1) + 2) - 90 * (i + 1) = 10 * 10^(i + 2) - 90 * i - 90 := by rw [goal_expr]
                        _ ≥ 10 * (100 + 90 * i) - 90 * i - 90 := by gcongr
                        _ = 1000 + 900 * i - 90 * i - 90 := by ring_nf
                        _ = 910 + 810 * i := by omega
                        _ ≥ 100 := by linarith
                    }
                  have helper':∀ k≥1,10 ^ (k + 2) - 90 * k-100≥0:=by exact fun k a ↦ le_sub_of_add_le (helper k a)
                  have helper'':10 ^ (k + 2) - 90 * k-100≥0:=by exact helper' k hk
                  -- Algebraic rearrangement
                  have t1:10 ^ (k + 2) - 90 * k - 100 + 81 * k + 81=10 ^ (k + 2) - 90 * k + 81 * k - 100 + 81:=by
                    refine Nat.add_left_inj.mpr ?_
                    exact Eq.symm (Nat.sub_add_comm (helper k hk))
                  have t2:10 ^ (k + 2) - 90 * k + 81 * k - 100 + 81=10 ^ (k + 2) - (90 * k - 81 * k) - 19:=by
                    omega
                  have t3:10 ^ (k + 2) - (90 * k - 81 * k) - 19=10 ^ (k + 2) - (9* k) - 19:=by
                    omega
                  rw [t1,t2,t3]
                _ = 10^(k + 2) - 9 * (k + 1) - 10 := by
                      rw [show 9 * (k + 1) = 9 * k + 9 by ring]
                      omega
              exact id (Eq.symm this)
            -- A(i) is divisible by 9 (by induction hypothesis)
            have dvd_A : 9 ∣ A k := Nat.dvd_of_mod_eq_zero hk'
            -- 81(i+1) is divisible by 9
            have dvd_81 : 9 ∣ 81 * (k + 1) :=
              Dvd.dvd.mul_right (by use 9; ring) (k + 1)
            -- 10*A(i) is divisible by 9
            have dvd_10A : 9 ∣ 10 * A k :=
              dvd_mul_of_dvd_right dvd_A 10
            -- Sum is divisible by 9
            have dvd_sum : 9 ∣ 10 * A k + 81 * (k + 1) :=
              dvd_add dvd_10A dvd_81
            -- A(i+1) ≡ 0 mod 9
            rw [← rel,hA] at dvd_sum
            simp at dvd_sum
            exact dvd_iff_mod_eq_zero.mp dvd_sum
          }
        have heq3:9*(curr/9)=curr:=by
          refine Nat.mul_div_cancel' ?_
          exact dvd_of_mod_eq_zero (heq1 k hk)
        rw [heq3]
        omega

    rw [h1]
    rw [h_mod]
    -- Simplify modulo 9 expression
    have h3 : 10 * n_w k = 9 * n_w k + n_w k := by ring
    rw [h3] -- decompose 10*n_w(k)
    rw [add_assoc]  -- group terms
    rw [Nat.add_right_comm]  -- rearrange terms
    rw [← add_assoc]  -- regroup
    rw [Nat.add_mod]  -- apply modulo to sum
    norm_num  -- simplify modulo 9 arithmetic
    rw [← h_mod]  -- apply digit sum property to n_w(k)
    exact ih  -- apply induction hypothesis
