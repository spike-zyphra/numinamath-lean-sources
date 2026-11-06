import Mathlib
/- Let $B$ be an integer representing the number base, where $B \ge 2$. We are looking for the largest 6-digit number $a_1a_2a_3a_4a_5a_6$ in base $B$. This means $a_642160 \neq 0$, and for all $i \in \{1, \dots, 6\}$, $a_i$ is an integer satisfying $0 \le a_i < B$. The number must satisfy the property that $a_k = a_{k-1} + a_{k-2}$ for $k \in \{3,4,5,6\}$. Let $x=a_1$ and $y=a_2$. The sequence of digits is then $x, y, x+y, x+2y, 2x+3y, 3x+5y$. All these digit values must be less than $B$. Determine the pair $(x,y)$ that forms the largest such 6-digit number.
Show that the solution for $(x,y)$ is given by $x = \lfloor (B-1)/3 \rfloor$ and $y = \lfloor ((B-1) - 3x)/5 \rfloor$. The largest number is $N = x B^5 + y B^4 + (x+y)B^3 + (x+2y)B^2 + (2x+3y)B + (3x+5y)$.

To verify, let $B=4$.
Then $x = \lfloor (4-1)/3 \rfloor = \lfloor 3/3 \rfloor = 1$.
$y = \lfloor ((4-1) - 3 \cdot 1)/5 \rfloor = \lfloor (3-3)/5 \rfloor = 0$.
So $(a_1, a_2) = (1,0)$.
The digits are $a_1=1, a_2=0, a_3=1+0=1, a_4=0+1=1, a_5=1+1=2, a_6=1+2=3$.
All digits are less than $4$. The number is $101123_4$.
This is $1 \cdot 4^5 + 0 \cdot 4^4 + 1 \cdot 4^3 + 1 \cdot 4^2 + 2 \cdot 4^1 + 3 \cdot 4^0 = 1024 + 0 + 64 + 16 + 8 + 3 = 1115_{10}$. -/
theorem number_theory_642160 (b x y : ℕ) (hb : b ≥ 2) (hx : x = (b - 1) / 3) (hy : y = ((b - 1) - 3 * x) / 5) : IsGreatest {N : ℕ | ∃ x y : ℕ, 3 * x + 5 * y < b ∧ N = x * b ^ 5 + y * b ^ 4 + (x + y) * b ^ 3 + (x + 2 * y) * b ^ 2 + (2 * x + 3 * y) * b + (3 * x + 5 * y)} (x * b ^ 5 + y * b ^ 4 + (x + y) * b ^ 3 + (x + 2 * y) * b ^ 2 + (2 * x + 3 * y) * b + (3 * x + 5 * y)):= by
  constructor
  .
    -- First part: Show that our candidate (x,y) is in the set
    simp
    use x, y
    refine ⟨?_, ?_⟩
    .
      -- Show that 3x + 5y < b (constraint satisfaction)
      subst x y
      -- Use division property: 3 * ((b-1)/3) ≤ b-1
      have g1 : 3 * ((b - 1) / 3) ≤ b - 1:= by exact Nat.mul_div_le (b - 1) 3
      -- Use division property: 5 * ((b-1 - 3*((b-1)/3))/5) ≤ b-1 - 3*((b-1)/3)
      have g2 : 5 * ((b - 1 - 3 * ((b - 1) / 3)) / 5) ≤ b - 1 - 3 * ((b - 1) / 3):= by exact Nat.mul_div_le (b - 1 - 3 * ((b - 1) / 3)) 5
      omega
    .
      -- Show that N equals the expected formula
      simp
  .
    -- Second part: Show that our candidate is the greatest element
    simp [upperBounds]
    intro N x1 y1 h hN
    subst N
    -- Case analysis: either x1 < (b-1)/3 or x1 ≥ (b-1)/3
    by_cases h1 : x1 < (b - 1) / 3
    .
      -- Case 1: x1 < (b-1)/3, show that increasing x1 by 1 gives a larger number
      -- All other terms are non-negative
      have g1 : y * b ^ 4 + (x + y) * b ^ 3 + (x + 2 * y) * b ^ 2 + (2 * x + 3 * y) * b + (3 * x + 5 * y) ≥ 0:= by positivity
      replace h1 : x1 + 1 ≤ (b - 1) / 3:= by omega
      -- Show that (x1+1)*b^5 + ... ≤ (x+1)*b^5
      suffices (x1 + 1) * b ^ 5 + y1 * b ^ 4 + (x1 + y1) * b ^ 3 + (x1 + 2 * y1) * b ^ 2 + (2 * x1 + 3 * y1) * b + (3 * x1 + 5 * y1) ≤ (x + 1) * b ^ 5 by linarith
      -- Helper lemma: if z < b, then z*b^n ≤ (b-1)*b^n
      have g2 : ∀ z n : ℕ, z < b → z * b ^ n ≤ (b - 1) * b ^ n:= by
        intro z n h
        replace h : z ≤ b - 1:= by omega
        have g : b ^ n ≥ 0:= by positivity
        exact Nat.mul_le_mul_right (b ^ n) h
      -- Apply the helper lemma to each term
      have g3:= g2 y1 4 (by linarith)
      have g4:= g2 (x1 + y1) 3 (by linarith)
      have g5:= g2 (x1 + 2 * y1) 2 (by linarith)
      have g6:= g2 (2 * x1 + 3 * y1) 1 (by linarith)
      have g7:= g2 (3 * x1 + 5 * y1) 0 (by linarith)
      simp at g7
      -- Show that (x1+1)*b^5 ≤ ((b-1)/3)*b^5
      replace h1 : (x1 + 1) * b ^ 5 ≤ (b - 1) / 3 * b ^ 5:= by
        have g : b ^ 5 ≥ 0:= by positivity
        exact Nat.mul_le_mul_right (b ^ 5) h1
      rw [hx]
      -- Show that the sum of all other terms is ≤ b^5
      suffices (b - 1) * b ^ 4 + (b - 1) * b ^ 3 + (b - 1) * b ^ 2 + (b - 1) * b + (b - 1) ≤ b ^ 5 by linarith
      -- Let c = b-1 and substitute b = c+1
      set c:= b - 1 with hc
      clear_value c
      replace hc : b = c + 1:= by omega
      subst b
      ring_nf
      linarith
    .
      -- Case 2: x1 ≥ (b-1)/3, so x1 = (b-1)/3
      simp at h1
      replace h1 : x1 = (b - 1) / 3:= by omega
      -- Since x1 = x, we must have y1 ≤ y for optimality
      have h2 : y1 ≤ y:= by omega
      -- Helper lemma: if p ≤ q, then p*b^n ≤ q*b^n
      have g : ∀ p q n : ℕ, p ≤ q → p * b ^ n ≤ q * b ^ n:= by
        intro p q n h
        have g : b ^ n ≥ 0:= by positivity
        exact Nat.mul_le_mul_right (b ^ n) h
      -- Apply the helper lemma to each term in the number representation
      have g1:= g x1 x 5 (by linarith)
      have g2:= g y1 y 4 (by linarith)
      have g3:= g (x1 + y1) (x + y) 3 (by linarith)
      have g4:= g (x1 + 2 * y1) (x + 2 * y) 2 (by linarith)
      have g5:= g (2 * x1 + 3 * y1) (2 * x + 3 * y) 1 (by linarith)
      have g6:= g (3 * x1 + 5 * y1) (3 * x + 5 * y) 0 (by linarith)
      simp at g6
      linarith
