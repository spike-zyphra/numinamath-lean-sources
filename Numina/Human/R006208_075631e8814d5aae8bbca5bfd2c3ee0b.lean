import Mathlib
open Nat

/-
In the prime factorization of $24!$, what is the exponent of $3$?  (Reminder: The number $n!$ is the product of the integers from 1 to $n$.  For example, $5!=5\cdot 4\cdot3\cdot2\cdot 1= 120$.) -/
theorem Algebra_608942
{k p : ℕ}
{q1 q2 : ℕ}
(hp : Nat.Prime p ∧ p > k / 4)
(hk : k = 20)
(hq1 : q1.Prime)
(hq2 : q2.Prime)
(hle : q1 ≤ q2)
(h : k * p + 1 = q1 * q2) :
(k * p).primeFactorsList = [2, 2, k / 4, p] ∧ (k * p + 1).primeFactorsList = [q1, q2] := by

  -- Substitute k with 20 using the equality hk
  rw [hk]

  -- Prove that 20 * p is equal to 2 * 2 * 5 * p using ring arithmetic
  have h_kp_eq : 20 * p = 2 * 2 * 5 * p := by ring

  -- Prove that p is greater than 5 by combining hp.2 and hk
  have h_p_gt_5 : p > 5 := by
    have p1 : p > k / 4 :=by exact hp.2
    have p2 : k / 4 = 5 := by rw [hk]
    exact lt_of_eq_of_lt (id (Eq.symm p2)) p1

  -- Prove the order relation between the prime factors 2, 2, 5, and p
  have h_order : 2 ≤ 2 ∧ 2 ≤ 5 ∧ 5 ≤ p := by
    constructor
    · simp
    constructor
    · simp
    · exact Nat.le_of_lt h_p_gt_5

  -- Lemma: For two primes p1 ≤ p2, the smallest factor of their product is p1
  have y (p1 p2:ℕ)(hp1:Nat.Prime p1)(hp2:Nat.Prime p2)(hp1p2:p1≤p2):(p1*p2).minFac=p1:=by
    let r:=(p1*p2).minFac
    have r1:r∣p1*p2:=by exact minFac_dvd (p1 * p2)
    have r2:p1∣p1*p2:=by exact Nat.dvd_mul_right p1 p2
    have r3:r≤p1:=by refine minFac_le_of_dvd (by exact Prime.two_le hp1) r2
    have hr:Nat.Prime r:=by
      refine minFac_prime ?_
      refine Ne.symm (Nat.ne_of_lt ?_)
      have t1:p1≥2:=by exact Prime.two_le hp1
      have t2:p2≥2:=by exact Prime.two_le hp2
      have t3:p1*p2≥2*2:=by exact Nat.mul_le_mul t1 t2
      linarith
    have r4:r∣p1∨r∣p2:=by refine (Nat.Prime.dvd_mul hr).mp r1

    -- Case analysis for when r divides p1 or p2
    cases r4
    case inl H=>
      have t1:r=1∨r=p1:=by exact (dvd_prime hp1).mp H
      have t2:r≥2:=by refine Prime.two_le hr
      omega
    case inr H=>
      have t1:r=1∨r=p2:=by exact (dvd_prime hp2).mp H
      have t2:r≥2:=by refine Prime.two_le hr
      have t3:r=p2:=by omega
      rw[t3] at r3
      apply le_antisymm at hp1p2
      have t4:p1=p2:=by tauto
      rw[t4,← pow_two]
      refine Prime.pow_minFac hp2 (by trivial)

  -- Prove that the prime factors list of 20 * p is [2, 2, 5, p]
  have h_factors1 : (20 * p).primeFactorsList = [2, 2, 5, p] := by
    have t:(20*p).minFac=2:=by
      refine (minFac_eq_two_iff (20 * p)).mpr (?_)
      rw[mul_comm]
      refine (Nat.Prime.dvd_mul ?_).mpr ?_
      trivial
      right
      trivial
    have t1:(20*p).primeFactorsList = 2::(20*p /2).primeFactorsList:=by
      unfold Nat.primeFactorsList
      have t2:20*p=(20*p-2).succ.succ:=by simp;omega
      rw[t2]
      simp
      have e1:20*p- 2 + 2=20*p:=by omega
      rw[e1,t]
      split_ands
      · refine dvd_sub' (by exact (minFac_eq_two_iff (20 * p)).mp t) (by trivial)
      · exact primeFactorsList.eq_def (20 * p / 2)
    have t2:20*p /2=10*p:=by refine Nat.div_eq_of_eq_mul_right (by trivial) (by ring)
    rw[t2] at t1
    rw[t1]
    refine (List.cons_inj_right 2).mpr ?_
    have t:(10*p).minFac=2:=by
      refine (minFac_eq_two_iff (10 * p)).mpr (?_)
      rw[mul_comm]
      refine (Nat.Prime.dvd_mul ?_).mpr ?_
      trivial
      right
      trivial
    have t1:(10*p).primeFactorsList = 2::(10*p /2).primeFactorsList:=by
      unfold Nat.primeFactorsList
      have t2:10*p=(10*p-2).succ.succ:=by simp;omega
      rw[t2]
      simp
      have e1:10*p- 2 + 2=10*p:=by omega
      rw[e1,t]
      split_ands
      · refine dvd_sub' (by exact (minFac_eq_two_iff (10 * p)).mp t) (by trivial)
      · exact primeFactorsList.eq_def (10 * p / 2)
    have t2:10*p /2=5*p:=by refine Nat.div_eq_of_eq_mul_right (by trivial) (by ring)
    rw[t2] at t1
    rw[t1]
    refine (List.cons_inj_right 2).mpr ?_
    have t:(5*p).minFac=5:=by
      apply y
      exact prime_five
      exact hp.1
      tauto

    have t1:(5*p).primeFactorsList = 5::(5*p /5).primeFactorsList:=by
      unfold Nat.primeFactorsList
      have t2:5*p=(5*p-2).succ.succ:=by simp;omega
      rw[t2]
      simp
      have e1:5*p- 2 + 2=5*p:=by omega
      rw[e1,t]
      split_ands
      · omega
      · exact primeFactorsList.eq_def (5* p / 5)
    have t2:5*p /5=p:=by refine Nat.div_eq_of_eq_mul_right (by trivial) (by ring)
    rw[t2] at t1
    rw[t1]
    refine (List.cons_inj_right 5).mpr ?_
    refine primeFactorsList_prime ?_
    tauto

  -- Prove the equality q1 * q2 = 20 * p + 1 using the given hypothesis h
  have h_prod : q1 * q2 = 20 * p + 1 := by exact Eq.symm (Mathlib.Tactic.Abel.subst_into_add (20 * p) 1 (k * p) 1 (q1 * q2)
  (congrFun (congrArg HMul.hMul (id (Eq.symm hk))) p) rfl h)

  -- Extract the prime properties of q1 and q2
  have h_prime1 : q1.Prime := hq1
  have h_prime2 : q2.Prime := hq2

  -- Prove that the product q1 * q2 is at least 2
  have hq₁q₂:q1*q2≥ 2:=by
    have t1:q1≥2:=by exact Prime.two_le hq1
    have t2:q2≥2:=by exact Prime.two_le hq2
    linarith

  -- Prove that the prime factors list of 20 * p + 1 is [q1, q2]
  have h_factors2 : (20 * p + 1).primeFactorsList = [q1, q2] := by
    rw [← hk,h]
    have t:(q1*q2).minFac=q1:=by
      apply y
      all_goals assumption

    have t1:(q1*q2).primeFactorsList = q1::(q1*q2 /q1).primeFactorsList:=by
      unfold Nat.primeFactorsList
      have t2:q1*q2=(q1*q2-2).succ.succ:=by simp;omega
      rw[t2]
      simp
      have e1:q1 * q2 - 2 + 2=q1*q2:=by omega
      rw[e1,t]
      simp
      exact primeFactorsList.eq_def (q1 * q2 / q1)
    have t2:q1*q2 /q1=q2:=by refine mul_div_right q2 (by exact Prime.pos hq1)
    rw[t2] at t1
    rw[t1]
    refine (List.cons_inj_right q1).mpr ?_
    exact primeFactorsList_prime hq2

  -- Combine the two prime factor list results to prove the main theorem
  exact ⟨h_factors1, h_factors2⟩
