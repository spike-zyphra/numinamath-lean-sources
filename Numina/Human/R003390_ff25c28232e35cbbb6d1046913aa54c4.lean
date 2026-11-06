import Mathlib

def f (n : ℕ) : ℕ := match n with
| 0 => 2
| 1 => 2
| n + 2 => f n * f (n + 1)

/-
A6. A sequence of numbers is constructed as follows:

The first number is 2. The second number is 2.

Each subsequent number is the product of its two predecessors.

The sequence thus becomes: $2, 2, 4, 8, 32, \ldots$

What is the last digit of the $2007^{\text{th}}$ number in this sequence?
(A) 0
(B) 2
(C) 4
(D) 6
(E) 8
 -/
theorem number_theory_175198 : f 2006 % 10 = 4 := by
  /-
  A6. We continue the sequence with only the last digits of the numbers: we find

  $2,2,4,8, \cdot 2, \cdot \cdot 6, \cdot 2, \cdot \cdot 2, \cdot 4, \cdot 8, \cdot 2, \cdot 6, \cdot 2$, etc. We see that a group of six digits repeats itself. Since $2007=334 \times 6+3$, the last digit of the 2007th number is equal to that of the third number, so 4. (C).
   -/
  let rec plus_6_congr_mod : ∀ n, f (n + 6) ≡ f n [MOD 10]
    | 0 => by decide
    | 1 => by decide
    | (n' + 2) => by
      unfold f
      gcongr
      . exact plus_6_congr_mod n'
      . exact plus_6_congr_mod (n' + 1)
  let rec plus_6_k_congr_mod n k : f (n + 6 * k) ≡ f n [MOD 10] :=
    match k with
    | 0 => rfl
    | k' + 1 =>
      have h1 := plus_6_congr_mod (n + 6 * k')
      have h2 := plus_6_k_congr_mod n k'
      h1.trans h2
  have := plus_6_k_congr_mod 2 334
  norm_num at this
  exact this
