import Mathlib


/--
The picture of the question is
n
↑
|15
|10 14
|6  9  13
|3  5  8  12
|1  2  4  7  11
+--------------→m
-/

-- Q 1 1
-- Q 2 3
-- Q 3 6
-- Q n p ↔ p is the value at position (1,n)
inductive Q : (n p : ℕ) → Prop where
  | OrigQ : Q 1 1
  | GoQ : ∀ n p, n > 1 → Q n p → Q (n + 1) (p + n + 1)
open Q

-- P 1 1 1
-- P 2 1 2
-- P 1 2 3
-- P m n p ↔ p is the value at position (m,n)
inductive P : (m n p : ℕ) → Prop where
  | M1 : Q n p → P 1 n p
  | Go : ∀ p, m > 1 → Q (m + n - 2) p → P m n (p + n)
open P

-- example : P 3 2 8 := by
--   repeat
--     constructor <;> try omega

lemma lemma1 (n : ℤ) : 2 ∣ n * (n + 1) := by
  by_cases h : 2 ∣ n
  . exact Dvd.dvd.mul_right h (n + 1)
  . have h : 2 ∣ n + 1 := by
      omega
    exact Dvd.dvd.mul_left h n

/- The squares of a squared paper are enumerated as follows:

![](https://cdn.mathpix.com/cropped/2024_04_17_a668d2eee50487b1b875g-1.jpg?height=406&width=459&top_left_y=999&top_left_x=316)

Devise a polynomial $p(m, n)$ of two variables $m, n$ such that for any positive integers $m$ and $n$ the number written in the square with coordinates $(m, n)$ will be equal to $p(m, n)$.-/
theorem number_theory_605333
  (m n r : ℕ) (mpos : m > 0) (npos : n > 0)
  : P m n r → r = ((m + n - 2) * (m + n - 1)) / 2 + n :=
by
  have l1 : ∀ n > 0, ∀ r, Q n r → r = ((n - 1) * n) / 2 + n := by
    intro n nh r q
    induction q with
    | OrigQ => omega
    | GoQ n p nh q ih =>
      simp
      rw [ih]
      qify
      rw [Nat.cast_sub]; push_cast
      rw [Int.cast_div]; push_cast
      rw [Int.cast_div]; push_cast
      ring_nf
      apply lemma1
      simp
      nth_rewrite 2 [show n = (n - 1 + 1 : ℤ) by linarith]
      apply lemma1
      simp
      omega
      omega
  intro p
  cases p with
  | M1 q =>
    simp
    have : (1 + n - 2) = n - 1 := by omega
    rw [this]
    apply l1
    assumption
    assumption
  | Go p mh q =>
    -- have : m + n - 2 = m - 2 + n := by
    --   omega
    -- rw [this] at q ⊢
    have := l1 _ ?_ _ q
    rw [this]
    qify
    repeat rw [Nat.cast_sub]; push_cast
    repeat rw [Int.cast_div]; push_cast
    linarith
    rw [show (m + n - 1 : ℤ) = ↑m + ↑n - 2 + 1 by omega]
    apply lemma1
    simp
    nth_rewrite 2 [show (↑m + ↑n - 2 : ℤ) = (↑m + ↑n - 2 - 1 + 1) by omega]
    apply lemma1
    simp
    all_goals omega
