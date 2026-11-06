import Mathlib

set_option maxHeartbeats 10000000

/- 1. Find the value of the Euler phi-function for each of the following integers:
a) 100
b) 256
c) 1001
d) \(2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13\)
e) \(10!\)
f) \(20!\)-/
theorem number_theory_4863 :
    (Nat.totient 100 = 40) ∧
    (Nat.totient 256 = 128) ∧
    (Nat.totient 1001 = 720) ∧
    (Nat.totient (2*3*5*7*11*13) = 5760) ∧
    (Nat.totient (Nat.factorial 10) = 829440) ∧
    (Nat.totient (Nat.factorial 20) = 416084687585280000):= by
  -- divide the goals
  constructor
  -- solve the goals
  decide
  constructor
  --use the formula to simplify the totient function
  rw [Nat.totient_eq_div_primeFactors_mul]
  have :Nat.primeFactors 256 = {2} := by native_decide
  rw [this]
  simp
  rw [Nat.totient_eq_div_primeFactors_mul]
  have :Nat.primeFactors 1001 = {7, 11, 13} := by native_decide
  rw [this]
  simp
  constructor
  rw [Nat.totient_eq_div_primeFactors_mul]
  have :Nat.primeFactors (2*3*5*7*11*13) = {2, 3, 5, 7, 11, 13} := by
    repeat rw [Nat.primeFactors_mul]
    all_goals norm_num
    aesop
  rw [this]
  simp
  have h1: Nat.primeFactors 10 = {2,5} := by native_decide
  have h2: Nat.primeFactors 9 = {3} := by native_decide
  have h3: Nat.primeFactors 8 = {2} := by native_decide
  have h4: Nat.primeFactors 6 = {2,3} := by native_decide
  have h5: Nat.primeFactors 4 = {2} := by native_decide
  have h6: Nat.primeFactors 12 = {2,3} := by native_decide
  have h7: Nat.primeFactors 14 = {2,7} := by native_decide
  have h8: Nat.primeFactors 15 = {3,5} := by native_decide
  have h9: Nat.primeFactors 16 = {2} := by native_decide
  have h10: Nat.primeFactors 18 = {2,3} := by native_decide
  have h11: Nat.primeFactors 20 = {2,5} := by native_decide
  -- unfold factorial
  constructor

  rw [Nat.totient_eq_div_primeFactors_mul]
  have :Nat.primeFactors (Nat.factorial 10) = {2, 3, 5, 7} := by
    rw [Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ]
    rw [Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul]
    simp
    any_goals norm_num
    rw [h1,h2,h3,h4,h5]
    aesop
  -- use the formula to simplify the totient function
  rw [this]
  simp
  decide

  -- use the same method
  rw [Nat.totient_eq_div_primeFactors_mul]
  have :Nat.primeFactors (Nat.factorial 20) = {2, 3, 5, 7 , 11, 13, 17,19} := by
    rw [Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ]
    rw [Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ]
    rw [Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul]
    rw [Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul,Nat.primeFactors_mul]
    simp
    any_goals norm_num
    rw [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
    aesop
  rw [this]
  simp
  decide
