import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.IntervalCases

open BigOperators Set Nat

/-How many sets of two or more consecutive positive integers have a sum of 15?-/

theorem AMC_Number_Theory_1168 (t: Finset (Finset Nat))(ht: ∀ s, s∈ t ↔ ((∃ a b, 0<a∧a<b∧ s=Finset.Ico a (b+1))∧ (∑ c∈s, c=15))): t.card=3:=by
--A set consists of consecutive positive integers with at least two elements means it is of the form Finset.Ico a (b+1) with 0< a< b.
--We prove two auxiliary lemma used.
--The first is that a+b-1 * b-a is always even.
  have h₀ (a b: Nat) (altb:a<b): Even ((a+b-1)*(b-a)):=by
    rw[even_mul]
    by_cases evena:Even a
    all_goals
      by_cases evenb:Even b
    simp_all
    · right;rw[even_sub];simp_all;linarith
    · left;rw[even_sub];simp;rw[add_comm,odd_add];simp_all;linarith
    · left;rw[even_sub];simp;rw[odd_add];simp_all;linarith
    · right;rw[even_sub,←not_iff_not];simp_all;linarith
--The second is that the result of summation of integral elements in [a,b) has a close form (a+b-1)*(b-a)/2.
  have aux (a b: ℕ) (hab:a < b):∑ c∈Finset.Ico a b, c = (a+b-1)*(b-a)/2:=by
    have hab':1≤b-a:=by rw[Nat.le_sub_iff_add_le];linarith;linarith
    symm
    rw[Nat.div_eq_iff_eq_mul_left]
    swap;norm_num;swap;rw[←even_iff_two_dvd,←add_succ_sub_one,←add_one];apply h₀;linarith
    rw[Finset.sum_Ico_eq_sum_range,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range, smul_eq_mul,Finset.sum_range_id,add_mul,Nat.div_mul_cancel,←Int.natCast_inj]
    simp only [cast_mul, cast_add, cast_ofNat]
    rw[Int.natCast_sub,Int.natCast_sub,Int.natCast_sub,Int.natCast_sub,Int.natCast_add]
    ring_nf
    all_goals
      try linarith
    exact even_iff_two_dvd.mp (even_mul_pred_self _)
--We set tans as the result of our t.
  set tans:Finset (Finset Nat):={Finset.Ico 1 6, Finset.Ico 4 7,Finset.Ico 7 9} with tansdef
--We prove the Key lemma :t=tans.
  have:t=tans:=by
    ext s;rw[ht,tansdef]
    symm
    constructor
--We prove that s∈tans implies s∈t, which is simpler.
    · intro hs;simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with hs|hs|hs
      all_goals
        rw[hs,aux];norm_num;swap;linarith
      use 1;simp only [zero_lt_one, true_and];use 5;simp only [one_lt_ofNat, reduceAdd, and_self]
      use 4;simp only [ofNat_pos, true_and];use 6;simp only [reduceLT, reduceAdd, and_self]
      use 7;simp only [ofNat_pos, true_and];use 8;simp only [Nat.lt_add_one, reduceAdd, and_self]
--We prove that s∈t implies s∈tans
    · intro hs
--We introduce several variable a,b and their assumptions.
      rcases hs with ⟨⟨a,b,⟨apos,⟨hab,sdef⟩⟩⟩,ssum⟩
      rw[sdef,aux,add_succ_sub_one] at ssum
      simp only [sdef,Finset.mem_insert, Finset.mem_singleton]
--We simplify our goals.
      pick_goal 2;linarith
      rw[Nat.div_eq_iff_eq_mul_left] at ssum
      norm_num at ssum
      swap;norm_num;swap
      rw[←even_iff_two_dvd,←add_succ_sub_one,←add_one]
      apply h₀;linarith
--We now rewrite the ssum condition as (a+b)*(b+1-a)
--Now we introduce a more explicit version of our lemma which solves the equations.
      have aux':(a=1∧b=5)∨(a=4∧b=6)∨(a=7∧b=8):=by
--As the product is 30, each term divides 30.
        have dvd30:30%(a+b)=0∧30%(b+1-a)=0:=by
          rw[←ssum];simp
        rw[←Nat.dvd_iff_mod_eq_zero,←Nat.dvd_iff_mod_eq_zero] at dvd30
        rcases dvd30 with ⟨h1,h2⟩
--We bound the factors above.
        have :=le_of_dvd (by norm_num) h1
        have :=le_of_dvd (by norm_num) h2
        have rlel:b+1-a≤a+b:=by simp;linarith
--(a+b) is a divisor of 30, so there are only 8 cases.
        have caseab:(a+b)=1∨(a+b)=2∨(a+b)=3∨(a+b)=5∨(a+b)=6∨(a+b)=10∨(a+b)=15∨(a+b)=30:=by
          interval_cases (a+b)
          all_goals
            revert h1
            decide
--(b+1-a) is a divisor of 30, so there are only 8 cases.
        have bsuba:(b+1-a)=1∨(b+1-a)=2∨(b+1-a)=3∨(b+1-a)=5∨(b+1-a)=6∨(b+1-a)=10∨(b+1-a)=15∨(b+1-a)=30:=by
          interval_cases (b+1-a)
          all_goals
            revert h2
            decide
        rcases caseab with h|h|h|h|h|h|h|h
        all_goals
          rcases bsuba with g|g|g|g|g|g|g|g
          all_goals
--Because the product is 30 and (b+1-a)≤a+b, we clear most cases
            revert ssum
            rw[h,g]
            simp only [reduceMul, reduceEqDiff, IsEmpty.forall_iff,forall_const]
            try linarith
--Now there are four cases left, we solve the equation case by case. We solve the equation h,g in a the rational field.
        all_goals
          rw[←Rat.natCast_inj,←Rat.natCast_inj,←Rat.natCast_inj,←Rat.natCast_inj,←Rat.natCast_inj,←Rat.natCast_inj]
          rw[←Int.natCast_inj] at h g
          rw[Int.natCast_sub] at g
--Clean redundant goals.
        all_goals
          try linarith
--Now we solve the linear equations system h and q.
        all_goals
          rw[Int.natCast_add,←Rat.intCast_inj] at h g
          simp at h g
          rw[←eq_sub_iff_add_eq] at h
          rw[h] at g;ring_nf at g;rw[←eq_sub_iff_add_eq',←eq_div_iff_mul_eq] at g
          norm_num at g
          rw[g] at h
          norm_num at h
          norm_cast at h g
        all_goals
          try rw[h,g]
          simp
        linarith
      rcases aux' with ⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩
      all_goals
      rw[ha,hb];simp
  rw[this,tansdef]
--Certainly, tans has three elements.
  decide