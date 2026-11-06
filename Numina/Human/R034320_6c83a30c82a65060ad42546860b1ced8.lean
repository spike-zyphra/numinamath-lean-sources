import Mathlib
open Mathlib
/--
The numbers $\log(a^3b^7)$, $\log(a^5b^{12})$, and $\log(a^8b^{15})$ are the first three terms of an [arithmetic sequence](https://artofproblemsolving.com/wiki/index.php/Arithmetic_sequence), and the $12^\text{th}$ term of the sequence is $\log{b^n}$. What is $n$?
$\mathrm{(A)}\ 40\qquad\mathrm{(B)}\ 56\qquad\mathrm{(C)}\ 76\qquad\mathrm{(D)}\ 112\qquad\mathrm{(E)}\ 143$
-/
theorem algebra_1189 (a b d base : ℝ) (hbase : 1 < base) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≠ 1) (n : ℕ) (h1 : Real.logb base (a^5 * b^12) = Real.logb base (a^3 * b^7) + d) (h2 : Real.logb base (a^8 * b^15) = Real.logb base (a^3 * b^7) + 2 * d) (h3 : Real.logb base (b^n) = Real.logb base (a^3 * b^7) + 11 * d) : n = 112 := by
  let A := Real.logb base a
  let B := Real.logb base b
  -- The first three terms of the arithmetic sequence are $3A + 7B$,
  have eq3 : Real.logb base (a ^ 3 * b ^ 7) = 3 * A + 7 * B := by
    rw [Real.logb_mul, Real.logb_pow, Real.logb_pow]
    · ring
    · norm_num; exact ne_of_gt ha
    · norm_num; exact ne_of_gt hb
  -- $5A + 12B$,
  have eq1 : Real.logb base (a ^ 5 * b ^ 12) = 5 * A + 12 * B := by
    rw [Real.logb_mul, Real.logb_pow, Real.logb_pow]
    · ring
    · norm_num; exact ne_of_gt ha
    · norm_num; exact ne_of_gt hb
  -- and $8A + 15B$,
  have eq2 : Real.logb base (a ^ 8 * b ^ 15) = 8 * A + 15 * B := by
    rw [Real.logb_mul, Real.logb_pow, Real.logb_pow]
    · ring
    · norm_num; exact ne_of_gt ha
    · norm_num; exact ne_of_gt hb
  -- and the $12^\text{th}$ term is $nB$.
  have eq4 : Real.logb base (b ^ n) = n * B := by
    rw [Real.logb_pow]
  -- Thus, $2(5A + 12B) = (3A + 7B) + (8A + 15B) ⇒ A = 2B$. 
  have eq5 : A = 2 * B := by linarith
  -- the $12^\text{th}$ term is $(9\cdot12 + 4)B = 112B = nB \Rightarrow n = 112\Rightarrow \boxed{D}$.
  have dst : 112 * B = n * B := by linarith
  have fin : B ≠ 0 := by
    unfold B
    apply Real.logb_ne_zero_of_pos_of_ne_one <;> assumption
  have := mul_right_cancel₀ fin dst
  rify
  exact this.symm