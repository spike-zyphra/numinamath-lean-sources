import Mathlib

open Nat


lemma lemma_1 {A X : ℕ} (hA : 0 < A) : 
  A * (X / A) ≤ X ∧ X < A * ((X / A) + 1) := by
  constructor
  · exact Nat.mul_div_le X A  -- Lower bound: A * (X / A) ≤ X
  ·
    -- X = A * (X / A) + X % A and X % A < A, so X < A * ((X / A) + 1)
    have h_mod : X % A < A := Nat.mod_lt X hA
    have h_div_mod : X = A * (X / A) + X % A := (Nat.div_add_mod X A).symm
    rw [mul_add, mul_one]
    linarith

/-
Let $A$ be a positive integer and $X$ be a natural number. Consider the arithmetic sequence where the $j$-th term (for $j=1, 2, 3, \ldots$) is given by $S_j = A \cdot (j-1)$. Thus, $S_1=0, S_2=A, S_3=2A$, and so on. We are interested in locating $X$ within this sequence.

1.  Determine the index $P$ such that $S_P \le X < S_{P+1}$. Show that $P = \lfloor X/A \rfloor + 1$.
2.  Determine the value of the $P$-th term, $S_P$. Show that $S_P = A \cdot \lfloor X/A \rfloor$.
3.  Determine the value of the $(P+1)$-th term, $S_{P+1}$. Show that $S_{P+1} = A \cdot (\lfloor X/A \rfloor + 1)$.
4.  Determine the difference $S_{P+1} - X$. Show that this difference is equal to $A - (X \pmod A)$, where $X \pmod A$ denotes the remainder $r$ when $X$ is divided by $A$ (i.e., $X = qA+r$ with $0 \le r < A$).
-/
theorem locate_X_in_arithmetic_sequence
  (A X : ℕ) (hA : 0 < A) :
  let P := X / A + 1
  let S := fun j : ℕ => A * (j - 1)
  (S P ≤ X ∧ X < S (P+1)) ∧
  (S P = A * (X / A)) ∧
  (S (P+1) = A * ((X / A) + 1)) ∧
  (S (P+1) - X = A - (X % A)) :=
let P := X / A + 1
let S := fun j : ℕ => A * (j - 1)

-- S P = A * (X / A)
have sp_calc : S P = A * (X / A) := by
  unfold S
  simp [P, add_sub_cancel]

-- S (P+1) = A * ((X / A) + 1)
have sp1_calc : S (P+1) = A * ((X / A) + 1) := by
  unfold S
  simp [P, add_sub_cancel]

-- Bounds for X
have bounds := lemma_1 hA
have lower_bound : S P ≤ X := by rw [sp_calc]; exact bounds.1
have upper_bound : X < S (P+1) := by rw [sp1_calc]; exact bounds.2

-- Compute the difference S (P+1) - X
have diff_calc : S (P+1) - X = A - (X % A) := by
  rw [sp1_calc]
  -- X = A * (X / A) + X % A
  have X_eq : X = A * (X / A) + X % A := (Nat.div_add_mod X A).symm
  -- Simplify division and modulus
  have div_simp : (A * (X / A) + X % A) / A = X / A := by rw [← X_eq]
  have mod_simp : (A * (X / A) + X % A) % A = X % A := by rw [← X_eq]
  -- Expand arithmetic and substitute
  rw [mul_add, mul_one]
  rw [X_eq]
  rw [div_simp, mod_simp]
  -- Use subtraction lemma
  exact Nat.add_sub_add_left (A * (X / A)) A (X % A)

-- Combine all the results
⟨⟨lower_bound, upper_bound⟩, sp_calc, sp1_calc, diff_calc⟩