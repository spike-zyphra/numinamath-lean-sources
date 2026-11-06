import Mathlib

/-Let b be an integer greater than 7. Let 𝑁 1 , 𝑁 2 , 𝑁 3 be three numbers
whose LSF-first (least significant digit first) digit lists in base 𝑏 are
[ 5 , 7 , 1 ] , [ 4 , 1 , 7 ] , and [ 1 , 6 ]  respectively. This means:
𝑁 1 = 5 ⋅ 𝑏 0 + 7 ⋅ 𝑏 1 + 1 ⋅ 𝑏 2
N 2 ​ =4⋅b 0 +1⋅b 1 +7⋅b 2
𝑁 3 = 1 ⋅ 𝑏 0 + 6 ⋅ 𝑏 1
Compute their sum: 𝑆 = 𝑁 1 + 𝑁 2 + 𝑁 3
Let: 𝑠 0 = 5 + 4 + 1 = 10
𝑠 1 = 7 + 1 + 6 = 14
𝑠 2 = 1 + 7 = 8
The sum 𝑆 can be written as: 𝑆 = 𝑠 2 𝑏 2 + 𝑠 1 𝑏 + 𝑠 0 = 8 𝑏 2 + 14 𝑏 + 10
Let 𝑟 0 , 𝑟 1 , 𝑟 2 , 𝑟 3 be digits calculated as follows:
𝑟 0 = 𝑠 0 m o d 𝑏 and 𝑐 0 = ⌊ 𝑠 0 / 𝑏 ⌋ So 𝑟 0 = 10 m o d 𝑏 and 𝑐 0 = ⌊ 10 / 𝑏 ⌋  𝑟 1 = ( 𝑠 1 + 𝑐 0 ) m o d 𝑏
 and 𝑐 1 = ⌊ ( 𝑠 1 + 𝑐 0 ) / 𝑏 ⌋ 𝑟 2 = ( 𝑠 2 + 𝑐 1 ) m o d 𝑏  and 𝑐 2 = ⌊ ( 𝑠 2 + 𝑐 1 ) / 𝑏 ⌋ 𝑟 3 = 𝑐 2
 ​ The final digit list representation depends on the values of 𝑟 0 , 𝑟 1 , 𝑟 2 , 𝑟 3 ​:
[ 𝑟 0 , 𝑟 1 , 𝑟 2 , 𝑟 3 ] if 𝑟 3 ≠ 0
[r 0 ​ ,r 1 ​ ,r 2 ​ ] if 𝑟 3 = 0  and ( 𝑟 2 ≠ 0  or 𝑆 ≠ 𝑟 2 𝑏 2 + 𝑟 1 𝑏 + 𝑟 0)
[ 𝑟 0 , 𝑟 1 ] if 𝑟 3 = 0 r 2 ​ =0, and ( 𝑟 1 ≠ 0  or 𝑆 ≠ 𝑟 1 𝑏 + 𝑟 0 )
[ 𝑟 0 ] if 𝑟 3 = 0 , r 2 ​ =0,  r 1 ​ =0 (in this case 𝑆 = 𝑟 0 ≠ 0since 𝑆 > 0)
This is equivalent to the list of digits of 8 𝑏 2 + 14 𝑏 + 10 in base 𝑏, LSF-first,
as produced by standard algorithms like Mat.digits in Lean, which omits trailing zeros from the MSF end,
ensuring the MSF digit is non-zero unless the number is 0.-/

def N1 (b : ℕ) : ℕ := 5 * b^0 + 7 * b^1 + 1 * b^2
def N2 (b : ℕ) : ℕ := 4 * b^0 + 1 * b^1 + 7 * b^2
def N3 (b : ℕ) : ℕ := 1 * b^0 + 6 * b^1

def S (b : ℕ) : ℕ := N1 b + N2 b + N3 b

lemma S_eq (b : ℕ) : S b = 8 * b^2 + 14 * b + 10 := by
  simp [S, N1, N2, N3]
  ring

def compute_digits (b : ℕ): List ℕ :=
  let s0 := 10
  let s1 := 14
  let s2 := 8
  let r0 := s0 % b
  let c0 := s0 / b
  let r1 := (s1 + c0) % b
  let c1 := (s1 + c0) / b
  let r2 := (s2 + c1) % b
  let c2 := (s2 + c1) / b
  let r3 := c2
  if r3 ≠ 0 then [r0, r1, r2, r3]
  else if r2 ≠ 0 ∨ S b ≠ r2 * b^2 + r1 * b + r0 then [r0, r1, r2]
  else if r1 ≠ 0 ∨ S b ≠ r1 * b + r0 then [r0, r1]
  else [r0]

theorem number_theory_640894 (b : ℕ) (hb : 7 < b) :
  Nat.digits b (S b) = compute_digits b:= by

  by_cases lb: b ≤ 14

  -- for the case when b ≤ 14, we check one by one
  .
    interval_cases b
    all_goals simp [compute_digits, S_eq]

  -- for the case 14 < b, we can compute all coefficients
  .
    simp at lb
    clear hb
    simp [compute_digits, S_eq]
    have g1: ¬ (¬b = 0 ∧ b ≤ 8 + (14 + 10 / b) / b) := by
      by_contra! f
      rcases f with ⟨f, g⟩
      absurd g
      simp
      rw [show 10 / b = 0 by apply Nat.div_eq_of_lt; omega]
      simp
      rw [show 14 / b = 0 by apply Nat.div_eq_of_lt; omega]
      omega
    have g2: ¬(8 + (14 + 10 / b) / b) % b = 0 ∨
          ¬8 * b ^ 2 + 14 * b + 10 = (8 + (14 + 10 / b) / b) % b * b ^ 2 + (14 + 10 / b) % b * b + 10 % b := by
      by_contra! f
      rcases f with ⟨f, g⟩
      rw [show 10 / b = 0 by apply Nat.div_eq_of_lt; omega] at f
      simp at f
      rw [show 14 / b = 0 by apply Nat.div_eq_of_lt; omega] at f
      simp at f
      rw [Nat.mod_eq_of_lt] at f
      norm_num at f
      omega
    simp [g1, g2]
    repeat rw [Nat.mod_eq_of_lt]
    have f1: 10 / b = 0 := by
      apply Nat.div_eq_of_lt
      omega
    simp [f1]
    have f2: 14 / b = 0 := by
      apply Nat.div_eq_of_lt
      omega
    simp [f2]
    clear *- lb
    rw [show 8 * b ^ 2 + 14 * b + 10 = 10 + b * (8 * b + 14) by ring]
    rw [Nat.digits_add]
    simp
    rw [show 8 * b + 14 = 14 + b * 8 by ring]
    rw [Nat.digits_add]
    simp
    apply Nat.digits_of_lt
    all_goals try omega
    rw [show 10 / b = 0 by apply Nat.div_eq_of_lt; omega]
    omega