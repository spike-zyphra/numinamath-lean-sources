import Mathlib


open BigOperators Finset Nat

/-
Let $k_0$ be a positive integer. Consider the sequence of positive natural numbers $x$,
in increasing order, such that $x$ is a multiple of 5, $x$ is not a multiple of 4,
and $x$ is not a multiple of 7. Let $q = (k_0-1) \div 18$ and $r = (k_0-1) \pmod{18}$.
Let $M = (1,2,3,5,6,9,10,11,13,15,17,18,19,22,23,25,26,27)$ be the ordered sequence of the 18
integers in $\{1, \dots, 28\}$ that are not divisible by 4 or 7. Let $m'_{r+1}$ be the $(r+1)$-th
term of $M$. Show that the $k_0$-th number in the described sequence of $x$ values
is $5 \cdot (28q + m'_{r+1})$.
-/


-- Define the sequence M: numbers in {1,..,28} not divisible by 4 or 7
def M : List ℕ :=
  [1,2,3,5,6,9,10,11,13,15,17,18,19,22,23,25,26,27]

-- Check M has 18 elements
lemma M_length : M.length = 18 := rfl

@[simp]
def M_mem (n : ℕ) : ℕ :=
  M[n % 18]'(by simp [M_length]; exact Nat.mod_lt n (by norm_num))

-- Predicate: y is a valid candidate (not divisible by 4 or 7)
def valid (y : ℕ) : Prop := y ≥ 1 ∧ ¬4 ∣ y ∧ ¬7 ∣ y

-- The y-sequence: valid y in increasing order
def y_seq (n : ℕ) : ℕ :=
  n / 18 * 28 + M_mem (n % 18)

-- define the x-sequence based on y-sequence
def x_seq (n : ℕ) : ℕ :=
  5 * y_seq (n - 1)


-- Prove that all numbers in M are not divisible by 4 or 7
@[simp]
lemma M_valid : ∀ n ∈ M, ¬4 ∣ n ∧ ¬7 ∣ n := by
  decide

-- Prove that all numbers in M are not divisible by 4
@[simp]
lemma M_valid1 : ∀ n : ℕ, (M_mem n) % 4 ≠ 0 := by
  intro n
  have : ¬ 4 ∣ M_mem n := by
    field_simp
  omega

-- Prove that all numbers in M are not divisible by 7
@[simp]
lemma M_valid2 : ∀ n : ℕ, (M_mem n) % 7 ≠ 0 := by
  intro n
  have : ¬ 7 ∣ M_mem n := by
    field_simp
  omega

/- prove that number x in x_seq is a multiple of 5, x is not a multiple of 4, and x is not a
multiple of 7 -/
lemma x_seq_valid (n : ℕ) : x_seq n % 5 = 0 ∧ x_seq n % 4 ≠ 0 ∧ x_seq n % 7 ≠ 0 := by
  constructor
  swap
  constructor
  all_goals unfold x_seq y_seq
  .
    have : M_mem ((n - 1) % 18) % 4 ≠ 0 := by exact M_valid1 ((n - 1) % 18)
    omega
  .
    have : M_mem ((n - 1) % 18) % 7 ≠ 0 := by exact M_valid2 ((n - 1) % 18)
    omega
  .
    omega




/- 5 * (28 * ((k_0 - 1) / 18) + M_mem (k_0 - 1)), number of x_seq is a multiple of 5, x is not a multiple of 4, and x is not a
multiple of 7, has been proved in x_seq_valid -/
theorem number_theory_639421 (k_0 : ℕ+) (q Mr': ℕ) (hq : q = (k_0 - 1) / 18)
    (hr : Mr' = M_mem (k_0 - 1)) : x_seq k_0 = 5 * (28 * q + Mr') := by

  -- rewrite q Mr' in the goa
  rw [hq, hr]

  -- Use the definition of x_seq and y_seq
  unfold x_seq y_seq
  simp
  bound
