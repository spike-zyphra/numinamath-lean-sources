import Mathlib
open Mathlib

/--
Find the smallest integer $k$ for which the conditions:
1. $a_1, a_2, a_3, \dots$ is a non-decreasing sequence of positive integers
2. $a_n = a_{n-1} + a_{n-2}$ for all $n > 2$
3. $a_9 = k$

are satisfied by more than one sequence.
-/

-- Define a predicate `p` for a sequence of integers satisfying the conditions
def p (f : ℕ → ℕ) k :=
  -- Condition 1: The sequence is non-decreasing
  (∀ m n : ℕ, m ≤ n → f m ≤ f n)
  -- Condition 2: All integers in the sequence are positive
  ∧ (∀ x, 0 < f x)
  -- Condition 3: The recurrence relation holds
  ∧ (∀ x, f (x + 2) = f (x + 1) + f x)
  -- Condition 4: The value at position 8 must be equal to k
  ∧ f 8 = k

-- Define the first Fibonacci-like sequence `ff1`
def ff1 (x : ℕ) :=
  match x with
  | 0 => 1
  | 1 => 35
  | x + 2 => ff1 (x + 1) + ff1 x

-- Define the second Fibonacci-like sequence `ff2`
def ff2 (x : ℕ) := 
  match x with
  | 0 => 22
  | 1 => 22
  | x + 2 => ff2 (x + 1) + ff2 x

-- Lemma: Given a least `x` that satisfies certain conditions, we deduce that x = 748
lemma numbertheory_719 (x : ℕ) (h : IsLeast { x | ∃ f1 f2, f1 ≠ f2 ∧ p f1 x ∧ p f2 x } x) : x = 748 := by
  -- Break down the assumption that `x` is the least such number
  cases' h with h1 h2
  rw [Set.mem_setOf] at h1
  cases' h1 with f1 rest
  cases' rest with f2 rest
  cases' rest with fd rest
  cases' rest with p1 p2
  rcases p1 with ⟨p11, ⟨p12, ⟨p13, p14⟩⟩⟩
  rcases p2 with ⟨p21, ⟨p22, ⟨p23, p24⟩⟩⟩
  
  -- From the recurrence relation (2), we can express `a9` as a linear combination of earlier terms
  have con1 : f1 8 = 13 * f1 0 + 21 * f1 1 := by
    simp only [p13]; ring
  have con2 : f2 8 = 13 * f2 0 + 21 * f2 1 := by
    simp only [p23]; ring
  
  -- If the initial terms of both sequences are equal, then the sequences must be identical
  have deter : f1 0 = f2 0 ∧ f1 1 = f2 1 → f1 = f2 := by
    intro al
    cases' al with a1 a2
    ext x
    induction x using Nat.strong_induction_on with
    | h n a =>
      cases n with
      | zero => exact a1
      | succ n =>
        cases n with
        | zero =>
          norm_num
          exact a2
        | succ n =>
          simp only [p13, p23]
          rw [a (n + 1) (by linarith), a n (by linarith)]
  
  -- Apply the decidable property to handle the cases where the sequences might not be equal
  have inst := Classical.propDecidable (f1 = f2)
  rw [← Decidable.not_imp_not] at deter
  push_neg at deter
  have ald : f1 0 ≠ f2 0 ∨ f1 1 ≠ f2 1 := by
    have vvv := deter fd
    by_cases vv : f1 0 = f2 0
    · right
      exact vvv vv
    · left
      exact vv

  -- Without loss of generality, assume `f1 0 < f2 0` and proceed with the argument
  wlog vg : f1 0 < f2 0 generalizing f1 f2
  · apply this f2 f1 <;> try tauto
    cases' Nat.eq_or_lt_of_le (Nat.le_of_not_lt vg) with kwd kwd
    · exfalso
      rw [p14] at con1
      rw [p24] at con2
      rw [con1, kwd, Nat.add_left_cancel_iff, Nat.mul_left_cancel_iff (by decide)] at con2
      apply deter fd (kwd.symm)
      exact con2
    exact kwd
  
  -- Define `k` as the ratio of the difference in the first terms of the sequences
  let k := (f1 1 - f2 1) / 13
  have aan : k * 13 = f1 1 - f2 1 ∧ k * 21 = f2 0 - f1 0 := by
    have ywu : 13 * (f2 0 - f1 0) = 21 * (f1 1 - f2 1) := by
      zify at *
      rw [Int.ofNat_sub (by zify; linarith), Int.ofNat_sub (by zify; linarith)]
      linarith
    have cns := Nat.dvd_mul_right 21 (f1 1 - f2 1)
    rw [← ywu] at cns
    have dns := Nat.dvd_mul_right 13 (f2 0 - f1 0)
    rw [ywu] at dns
    have wwa := Nat.Coprime.dvd_of_dvd_mul_left (by decide) cns
    have wwb := Nat.Coprime.dvd_of_dvd_mul_left (by decide) dns
    have zza := Nat.div_mul_cancel wwa
    have zzb := Nat.div_mul_cancel wwb
    have asv : (13 * (f2 0 - f1 0)) / 21 = (21 * (f1 1 - f2 1)) / 21 := congrFun (congrArg HDiv.hDiv ywu) 21
    rw [Nat.mul_div_cancel_left _ (by decide)] at asv
    have avs : (13 * (f2 0 - f1 0) / 21) / 13 = (f1 1 - f2 1) / 13 := congrFun (congrArg HDiv.hDiv asv) 13
    rw [Nat.mul_div_assoc _ wwa, Nat.mul_div_cancel_left _ (by decide)] at avs
    rw [avs] at zza
    have hk : k = (f1 1 - f2 1) / 13 := rfl
    rw [← hk] at zza
    conv at zzb =>
      lhs
      rw [← hk]
    have yyb := @Nat.sub_add_cancel (f1 1) (f2 1) (by linarith)
    rw [← zzb] at yyb
    have yya := @Nat.sub_add_cancel (f2 0) (f1 0) (by linarith)
    rw [← zza] at yya
    tauto
  
  -- Continue by proving the goal with two witnesses
  cases' aan with aan aam
  rw [mem_lowerBounds] at h2
  simp_rw [Set.mem_setOf] at h2
  have ini := p11 0 1 (by decide)
  have int := p21 0 1 (by decide)
  
  -- Prove `x ≤ 748` by providing two valid sequences
  have wit1 : ∀ n m, n < m → ff1 n < ff1 m := by
    intros n m
    revert n
    induction m using Nat.strong_induction_on with
    | h m a =>
      intros n hn
      cases m with
      | zero => linarith
      | succ m =>
        cases m with
        | zero =>
          rw [(Nat.lt_one_iff.mp hn : n = 0)]
          decide
        | succ m =>
          simp only [ff1]
          cases' Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hn) with ar ar
          · rw [ar]
            by_cases jd : m = 0
            · simp only [jd, ff1]
              decide
            have := a m (by linarith) 0 (Nat.zero_lt_of_ne_zero jd)
            simp only [ff1] at this
            linarith
          have := a (m + 1) (lt_add_one (m + 1)) n ar
          exact Nat.lt_add_right (ff1 m) this

  -- Similarly, prove that `ff2` is non-decreasing
  have wit2 : ∀ n m, n < m → ff2 n ≤ ff2 m := by
    intros n m
    revert n
    induction m using Nat.strong_induction_on with
    | h m a =>
      intros n hn
      cases m with
      | zero => linarith
      | succ m =>
        cases m with
        | zero =>
          rw [(Nat.lt_one_iff.mp hn : n = 0)]
          decide
        | succ m =>
          simp only [ff2]
          cases' Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hn) with ar ar
          · rw [ar]
            by_cases jd : m = 0
            · simp only [jd, ff2]
              decide
            have := a m (by linarith) 0 (Nat.zero_lt_of_ne_zero jd)
            simp only [ff2] at this
            linarith
          have := a (m + 1) (lt_add_one (m + 1)) n ar
          exact Nat.le_add_right_of_le this
  
  -- Using these witnesses, conclude the proof
  have expl := h2 748 (by
    exists ff1
    exists ff2
    constructor
    · intro ghs
      have : ff1 0 = ff2 0 := by rw [ghs]
      simp only [ff1, ff2] at this
      norm_num at this
    constructor
    · rw [p]
      constructor
      · intros n m hnm
        cases' Nat.eq_or_lt_of_le hnm with ddd ddd
        · rw [ddd]
        have := wit1 _ _ ddd
        exact Nat.le_of_succ_le (wit1 n m ddd)
      constructor
      · intro x
        cases x with
        | zero => decide
        | succ x =>
          have := wit1 0 (x + 1) (Nat.zero_lt_succ x)
          simp only [ff1] at this
          exact Nat.zero_lt_of_lt this
      constructor
      · intro x
        simp only [ff1]
      · decide
    · rw [p]
      constructor
      · intros n m hnm
        cases' Nat.eq_or_lt_of_le hnm with ddd ddd
        · rw [ddd]
        have := wit1 _ _ ddd
        exact wit2 n m ddd
      constructor
      · intro x
        cases x with
        | zero => decide
        | succ x =>
          have := wit2 0 (x + 1) (Nat.zero_lt_succ x)
          simp only [ff2] at this
          exact Nat.zero_lt_of_lt this
      constructor
      · intro x
        simp only [ff2]
      · decide)
  
  -- Prove the final goal using omega
  -- because the rest is simple arithmetic
  have jssb := p12 0
  have jssa := p22 0
  omega