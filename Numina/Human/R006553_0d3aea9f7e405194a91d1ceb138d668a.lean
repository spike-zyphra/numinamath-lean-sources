import Mathlib

/-
Let $k$ be a positive integer. Determine the number of digits in the base-ten representation of $8^k \cdot 5^{2k} \cdot 15^k$. Show that this number is equal to $\lfloor k \log_{10} 3 \rfloor + 3k + 1$.
-/


--We first have the following two lemmas about the Nat.log.
--Both follow from the basic definition 
lemma l1 (a b : ℕ) (apos: 0 < a): Nat.log 10 (10^b * a) = Nat.log 10 a + b := by 
  
  induction' b with b hb

  simp

  rw [pow_succ]
  have : (10 ^ b * 10 * a) = 10 ^ b * a * 10 := by ring
  rw [this]
  rw [Nat.log_mul_base]
  rw [hb]
  ring
  linarith
  positivity
lemma l2 (k:ℕ) : Nat.log 10 (3^k) = ⌊↑k * Real.logb 10 3⌋ := by 

  have t1 : 0 ≤ ⌊↑k * Real.logb 10 3⌋ := by 
    refine Int.floor_nonneg.mpr ?_  
    refine Right.mul_nonneg ?_ ?_
    norm_cast
    exact Nat.zero_le k
    refine Real.logb_nonneg ?_ ?_
    norm_num
    norm_num

  have t2: ⌊↑k * Real.logb 10 3⌋.toNat = ⌊↑k * Real.logb 10 3⌋ := by 
    refine Int.toNat_of_nonneg ?_
    exact t1

  --We use the property of Nat.log.
  have cla : (Nat.log 10 (3 ^ k)) = ⌊↑k * Real.logb 10 3⌋.toNat := by 
    rw [Nat.log_eq_iff]
    rify at t2 ⊢
    
    constructor

    refine (Real.pow_le_iff_le_log ?_ ?_).mpr ?_
    linarith
    positivity
    rw [t2]
    have l1: ⌊↑k * Real.logb 10 3⌋ ≤ ↑k * Real.logb 10 3 := by exact Int.floor_le (↑k * Real.logb 10 3)
    have l2: ⌊↑k * Real.logb 10 3⌋ * Real.log 10 ≤ ↑k * Real.logb 10 3 * Real.log 10 := by 
      refine mul_le_mul_of_nonneg_right l1 ?_
      positivity
    have l3: ↑k * Real.logb 10 3 * Real.log 10 = Real.log (3 ^ k) := by 
      simp
      rw [← Real.log_div_log]
      field_simp
    linarith
    
    refine Real.lt_pow_of_log_lt ?_ ?_
    norm_num
    push_cast
    rw [t2]
    norm_cast
    
    have l1 : ↑k * Real.logb 10 3 < @HAdd.hAdd ℤ ℤ ℤ instHAdd ⌊↑k * Real.logb 10 3⌋ 1 := by simp
    have l2 : ↑k * Real.logb 10 3 * Real.log 10 < ↑(⌊↑k * Real.logb 10 3⌋ + 1) * Real.log 10 := by 
      refine mul_lt_mul_of_pos_of_nonneg' l1 ?_ ?_ ?_
      trivial
      positivity
      norm_cast
      linarith
    have l3 : Real.log ((3 ^ k)) = ↑k * Real.logb 10 3 * Real.log 10 := by
      simp
      rw [← Real.log_div_log]
      field_simp
    rify at l3
    simp at l3 ⊢
    norm_cast at l3 ⊢
    rw [l3]
    exact l2
    

    right
    norm_num

  zify at cla
  rw [cla]
  simp
  exact t1



theorem number_theory_638441 (k:ℕ) (kpos : 0 < k):
  (Nat.digits 10 (8^k * 5^(2*k)*15^k)).length = ⌊ k * Real.logb 10 3⌋ + 3*k + 1 := by

  --8 ^ k * 5 ^ (2 * k) * 15 ^ k = 3000^k.
  have e1 : 8 ^ k * 5 ^ (2 * k) * 15 ^ k = 10 ^ (3 * k) * 3 ^ k := by
    rw [pow_mul]
    rw [pow_mul]
    norm_num
    rw [← mul_pow]
    rw [← mul_pow]
    rw [← mul_pow]
    norm_num

  rw [e1]

  --Now we use the formula for the length of digits and then apply l1 and l2.
  rw [Nat.digits_len]
  field_simp
  rw [l1]
  push_cast
  rw [l2]
  positivity
  linarith
  simp
