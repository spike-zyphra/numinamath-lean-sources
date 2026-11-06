import Mathlib

/- Inductively definition of what is on board -/
inductive OnBoard (p q : ℕ) : ℝ → Prop where
  | Start1 : OnBoard p q √p
  | Start2 : OnBoard p q √q
  | ByAdd : a ≠ b → OnBoard p q a → OnBoard p q b → OnBoard p q (a + b)
  | BySub : a ≠ b → OnBoard p q a → OnBoard p q b → OnBoard p q (a - b)
  | ByMul : a ≠ b → OnBoard p q a → OnBoard p q b → OnBoard p q (a * b)
open OnBoard

lemma OnBoard_comm : OnBoard p q x → OnBoard q p x
| Start1 => Start2
| Start2 => Start1
| ByAdd h a b => ByAdd h (OnBoard_comm a) (OnBoard_comm b)
| BySub h a b => BySub h (OnBoard_comm a) (OnBoard_comm b)
| ByMul h a b => ByMul h (OnBoard_comm a) (OnBoard_comm b)

-- Step 1. generate q - p.
lemma OnBoard_sub (neq : p ≠ q) (ppos : p > 0) (qpos : q > 0) : OnBoard p q (q - p) := by
  have neq' : √q ≠ √p := by
    field_simp
    omega
  have sqrtadd : OnBoard p q (√q + √p) := ByAdd neq' Start2 Start1
  have sqrtsub : OnBoard p q (√q - √p) := BySub neq' Start2 Start1
  have : (√q - √p) * (√q + √p) = q - p := by
    ring_nf
    repeat rw [Real.sq_sqrt]
    all_goals norm_cast; simp
  rw [←this]
  apply ByMul
  . intro c
    have : √↑q - √↑q = √↑p + √↑p := by linarith
    have : 2 * √p = 0 := by linarith
    have : √p = 0 := by linarith
    have : p = 0 := by
      apply_fun (fun x => x ^ 2) at this
      simp at this
      omega
    subst this
    simp at ppos
  . assumption
  . assumption

-- Step 2. generate √(pq)
lemma OnBoard_sqrt_mul (neq : p ≠ q) : OnBoard p q √(p * q) := by
  have : √(p * q) = √p * √q := by
    refine Real.sqrt_mul' ↑p ?_
    simp
  rw [this]
  constructor
  . field_simp
    omega
  constructor
  constructor

-- Step 3. generate p * √q
lemma OnBoard_mul_sqrt (neq : p ≠ q) (pPrime : p.Prime) (qPrime : q.Prime) : OnBoard p q (p*√q) := by
  have : p * √q = √(p*q) * √p := by
    field_simp
    rw [mul_assoc, mul_comm √q, ←mul_assoc]
    simp
  rw [this]
  constructor
  . intro c
    simp at c
    have : q = 1 := by
      apply_fun (fun x => x / √p) at c
      rw [mul_comm, mul_div_assoc, div_self] at c
      simp at c
      omega
      simp
      exact Nat.Prime.ne_zero pPrime
    subst this
    norm_num at qPrime
  . exact OnBoard_sqrt_mul neq
  . constructor

lemma OnBoard_mul_sqrt' (neq : p ≠ q) (pPrime : p.Prime) (qPrime : q.Prime) : OnBoard p q (q*√p) := by
  apply OnBoard_comm
  apply OnBoard_mul_sqrt
  omega
  assumption
  assumption

  lemma OnBoard_add_sqrt_mul_helper (neq : p ≠ q) (pPrime : p.Prime) (qPrime : q.Prime) : OnBoard p q (↑p * √(↑p * ↑q)) := by
    field_simp
    rw [mul_comm √p, ←mul_assoc]
    constructor
    . intro c
      have : √(p * q) = 1 := by
        field_simp
        apply_fun (fun x => x / √ p) at c
        rw [mul_comm, mul_div_assoc, div_self] at c
        simp at c
        linarith
        simp
        exact Nat.Prime.ne_zero pPrime
      have : p * q = 1 := by
        rify
        exact Real.sqrt_eq_one.mp this
      have : p ≤ 1 := by
        by_contra h
        simp at h
        have : p * q > 1 := by
          refine Right.one_lt_mul' h ?_
          by_contra h
          simp at h
          interval_cases q
          <;> simp at this
          subst this
          simp at h
        omega
      interval_cases p
      simp at *
      simp at *
      subst c
      norm_num at pPrime
    . exact OnBoard_mul_sqrt neq pPrime qPrime
    . exact Start1


-- Step 4 : generate (p + q)√(pq)
lemma OnBoard_add_sqrt_mul (neq : p ≠ q) (pPrime : p.Prime) (qPrime : q.Prime) : OnBoard p q ((p + q)*√(p * q)) := by
  rw [add_mul]
  apply ByAdd
  . intro c
    field_simp at c
    simp [neq] at c
    rcases c with h|h
    <;> subst h
    . norm_num at pPrime
    . norm_num at qPrime
  . exact OnBoard_add_sqrt_mul_helper neq pPrime qPrime
  . apply OnBoard_comm
    rw [mul_comm (p : ℝ)]
    exact OnBoard_add_sqrt_mul_helper (id (Ne.symm neq)) qPrime pPrime

-- Step 5 : generate 2pq
lemma OnBoard_2pq (neq : p ≠ q) (pPrime : p.Prime) (qPrime : q.Prime) : OnBoard p q (2*p*q) := by
  have : 2*p*q = 2*p*q + (p + q)*√(p*q) - (p + q)*√(p*q) := by
    linarith
  rw [this]
  apply BySub
  . intro c
    field_simp at c
    simp at c
    rcases c with h|h
    <;> subst h <;> norm_num at *
  have : 2 * ↑p * ↑q + (↑p + ↑q) * √(↑p * ↑q) = (√p + √q) * (q*√p + p*√q) := by
    conv =>
      rhs
      rw [add_mul, mul_add, mul_add]
    rw [mul_comm (q : ℝ), ←mul_assoc, Real.mul_self_sqrt]
    rw [mul_comm (p : ℝ) √q, ←mul_assoc √q √q, Real.mul_self_sqrt]
    ring_nf
    simp
    rw [←mul_assoc, ←mul_assoc]
    exact Nat.cast_nonneg' q
    exact Nat.cast_nonneg' p
  rw [this]
  constructor
  . intro c
    have h1 : q * √p > √p := by
      apply lt_mul_left
      simp
      exact Nat.Prime.pos pPrime
      simp
      exact Nat.Prime.one_lt qPrime
    have h2 : p * √q > √q := by
      apply lt_mul_left
      simp
      exact Nat.Prime.pos qPrime
      simp
      exact Nat.Prime.one_lt pPrime
    have : √↑p + √↑q < ↑q * √↑p + ↑p * √↑q := by
      exact add_lt_add h1 h2
    linarith
  . constructor
    . simp
      omega
    . constructor
    . constructor
  . constructor
    . intro c
      have : ↑q = ↑p * √↑q / √↑p := by
        refine eq_div_of_mul_eq ?_ c
        simp
        exact Nat.Prime.ne_zero pPrime
      have : ↑q = ↑p / √↑p * √↑q := by
        ring_nf at this ⊢
        assumption
      have : q / √↑q = ↑p / √↑p := by
        refine (div_eq_iff ?_).mpr this
        simp
        exact Nat.Prime.ne_zero qPrime
      repeat rw [Real.div_sqrt] at this
      simp at this
      omega
    . exact OnBoard_mul_sqrt' neq pPrime qPrime
    . exact OnBoard_mul_sqrt neq pPrime qPrime
  . exact OnBoard_add_sqrt_mul neq pPrime qPrime

/- Most important lemma in this proof. -/
lemma OnBoard_gcd {m n : ℕ} (nh : OnBoard p q n) (mh : OnBoard p q m) : OnBoard p q (Nat.gcd n m) := by
  by_cases zm : m = 0
  . subst zm
    simp
    assumption
  by_cases zn : n = 0
  . subst zn
    simp
    assumption
  by_cases h : m ≤ n
  . have : n.gcd m = (n - m).gcd m := by
      exact Eq.symm (Nat.gcd_sub_self_left h)
    rw [this]
    by_cases mn : m = n
    . subst mn
      simp
      assumption
    apply OnBoard_gcd
    . rw [Nat.cast_sub]
      apply BySub
      simp
      omega
      assumption
      assumption
      omega
    . assumption
  . simp at h
    have : n.gcd m = n.gcd (m - n) := by
      refine Eq.symm (Nat.gcd_sub_self_right ?_)
      omega
    rw [this]
    apply OnBoard_gcd
    . assumption
    . rw [Nat.cast_sub]
      apply BySub
      simp
      omega
      assumption
      assumption
      omega

/- Let $p$ and $q$ be distinct prime numbers such that $q-p > 2$. The numbers $\sqrt{p}$ and $\sqrt{q}$ are written on the board. You are allowed to add to the board the sum, difference, or product of any two *different* numbers already written on the board. Prove that you can write the number 1 on the board. -/
theorem number_theory_638031
  (p q : ℕ)
  (pPrime : p.Prime)
  (qPrime : q.Prime)
  (pq : q - p > 2)
  : OnBoard p q 1 :=
by
  have : OnBoard p q (Nat.gcd (q - p) (2 * p * q)) := by
    apply OnBoard_gcd
    . rw [Nat.cast_sub]
      apply OnBoard_sub
      omega
      exact Nat.Prime.pos pPrime
      omega
      omega
    . simp
      refine OnBoard_2pq ?_ pPrime qPrime
      omega
  have gcdBoard : OnBoard p q (Nat.gcd (q - p) 2) := by
    have h : p.Coprime q := by
      rw [show p = p^1 by linarith, show q = q^1 by linarith]
      apply Nat.coprime_pow_primes
      <;> try assumption
      omega
    repeat rw [Nat.Coprime.gcd_mul_right_cancel_right] at this
    . assumption
    . refine (Nat.coprime_sub_self_right ?_).mpr ?_
      omega
      assumption
    . refine (Nat.coprime_self_sub_right ?_).mpr ?_
      omega
      exact Nat.coprime_comm.mp h
  by_cases p2 : p = 2
  . have : q ≠ 2 := by omega
    have : Odd q := by
      exact Nat.Prime.odd_of_ne_two qPrime this
    have : Odd (q - 2) := by
      refine Nat.Odd.sub_even ?_ this ?_
      omega
      simp
    subst p2
    have : (q - 2).gcd 2 = 1 := by
      apply Nat.coprime_two_right.mpr
      assumption
    simp [this] at gcdBoard
    assumption
  . have : (q - p).gcd 2 = 2 := by
      have : Even (q - p) := by
        refine (Nat.even_sub ?_).mpr ?_
        omega
        constructor
        . intro h
          exfalso
          have : q = 2 := by exact (Nat.Prime.even_iff qPrime).mp h
          omega
        . intro h
          exfalso
          have : p = 2 := by exact (Nat.Prime.even_iff pPrime).mp h
          omega
      refine Nat.gcd_eq_right ?_
      exact even_iff_two_dvd.mp this
    simp [this] at gcdBoard
    have H : OnBoard p q ((√p + 2*√q) * (√p + √q)) := by
      constructor
      . intro c
        field_simp at c
        apply_fun (fun x => x / √q) at c
        rw [mul_div_assoc, div_self] at c
        simp at c
        simp
        exact Nat.Prime.ne_zero qPrime
      . constructor
        . intro c
          apply_fun (fun x => x ^ 2) at c
          rw [mul_pow] at c
          norm_num at c
          norm_cast at c
          subst c
          apply Nat.not_prime_mul ?_ ?_ pPrime
          simp
          exact Nat.Prime.ne_one qPrime
        . constructor
        . constructor
          . intro c
            apply_fun (fun x => x ^ 2) at c
            norm_num at c
            norm_cast at c
            subst c
            norm_num at qPrime
          . assumption
          . constructor
      . constructor
        . intro c
          simp at c
          omega
        . constructor
        . constructor
    have : (√p + 2*√q) * (√p + √q) = p + 2 * q + 3 * √(p*q) := by
      simp
      ring_nf
      field_simp
    rw [this] at H
    have H' : OnBoard p q (2 * √(↑p * ↑q) + √(↑p * ↑q)) := by
      constructor
      . intro c
        apply_fun (fun x =>  x / √(↑p * ↑q)) at c
        rw [mul_div_assoc, div_self] at c
        simp at c
        simp
        constructor
        . exact Nat.Prime.ne_zero pPrime
        . exact Nat.Prime.ne_zero qPrime
      . constructor
        . intro c
          apply_fun (fun x => x ^ 2) at c
          rw [Real.sq_sqrt] at c
          norm_num at c
          norm_cast at c
          have : p ≤ 4 := by
            apply Nat.le_of_dvd
            simp
            use q
          interval_cases p <;> try norm_num at pPrime
          have : q = 2 := by omega
          subst this
          simp at pq
          omega
          norm_cast
          simp
        . assumption
        . simp
          constructor
          . simp
            omega
          . constructor
          . constructor
      . simp
        constructor
        . simp
          omega
        . constructor
        . constructor
    have : 2 * √(↑p * ↑q) + √(↑p * ↑q) = 3 * √(↑p * ↑q) := by linarith
    rw [this] at H'
    have : OnBoard p q (↑p + 2 * ↑q + 3 * √(↑p * ↑q) - 3 * √(↑p * ↑q)) := by
      apply BySub
      . simp
        intro c
        norm_cast at c
        omega
      . assumption
      . assumption
    simp at this
    have : Odd (p + 2 * q) := by
      refine Nat.odd_add.mpr ?_
      constructor
      . intro _
        simp
      . intro _
        exact Nat.Prime.odd_of_ne_two pPrime p2
    have : OnBoard p q (Nat.gcd 2 (p + 2 * q)) := by
      apply OnBoard_gcd gcdBoard
      simp
      assumption
    have r : Nat.gcd 2 (p + 2 * q) = 1 := by
      apply Nat.coprime_two_left.mpr
      assumption
    simp [r] at this
    assumption
