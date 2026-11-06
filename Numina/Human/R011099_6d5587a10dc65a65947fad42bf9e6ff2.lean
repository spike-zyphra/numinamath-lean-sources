import Mathlib

open Finset Nat

/-- Let $L_{1}=1, L_{2}=3$, and $L_{n+2}=L_{n+1}+L_{n}$ for $n\geq 1$. How many terms in the
sequence $L_{1}, L_{2}, L_{3},...,L_{2023}$ are even?

$\textbf{(A) }673\qquad\textbf{(B) }1011\qquad\textbf{(C) }675\qquad\textbf{(D) }1010
\qquad\textbf{(E) }674$ -/
theorem number_theory_94726 (L : ℕ → ℕ) (hL1 : L 1 = 1) (hL2 : L 2 = 3)
    (hL : ∀ n, L (n + 2) = L (n + 1) + L n) : {n ∈ Icc 1 2023 | Even (L n)}.card = 674 := by

  -- Let $s$ be the set of all $n$ in the interval $[1, 2023]$ such that $L_n$ is even.
  set s := {n ∈ Icc 1 2023 | Even (L n)}

  -- From the recursive definition, we see that $L_3 = 4$.
  have hL3 : L 3 = 4 := by rw [hL, hL1, hL2]

  -- Applying the recursive definition of $L$ to $L_{n + 3}$ twice, we see that
  -- $L_{n + 3} = 2L_{n + 1} + L_n$.
  have {n} : L (n + 3) = 2 * L (n + 1) + L n := by
    rw [hL, hL]
    ring

  -- This means that $L_{n + 3} \equiv L_n \pmod 2$.
  have L_add_three_mode_two {n} : L (n + 3) % 2 = L n % 2 := by
    rw [this]
    omega

  -- Repeatedly using this fact, we see that $L_{3k} \equiv L_3 \pmod 2$.
  have {k} : L (3 * k) % 2 = L 3 % 2 := by
    induction k with
    | zero => rw [L_add_three_mode_two]
    | succ k ih => rw [Nat.mul_succ, L_add_three_mode_two, ih]

  -- Which means that $L_{3k} \equiv 0 \pmod 2$.
  have L_three_mul_mod_two {k} : L (3 * k) % 2 = 0 := by
    rw [this, hL3]

  -- Repeatedly using this fact, we see that $L_{3k + 1} \equiv L_1 \pmod 2$.
  have {k} : L (3 * k + 1) % 2 = L 1 % 2 := by
    induction k with
    | zero => rw [hL1]
    | succ k ih => rw [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 3, ←Nat.add_assoc, L_add_three_mode_two, ih]

  -- Which means that $L_{3k + 1} \equiv 1 \pmod 2$.
  have L_three_mul_add_one_mod_two {k} : L (3 * k + 1) % 2 = 1 := by
    rw [this, hL1]

  -- Repeatedly using this fact, we see that $L_{3k + 2} \equiv L_2 \pmod 2$.
  have {k} : L (3 * k + 2) % 2 = L 2 % 2 := by
    induction k with
    | zero => rw [hL2]
    | succ k ih => rw [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 3, ←Nat.add_assoc, L_add_three_mode_two, ih]

  -- Which means that $L_{3k + 2} \equiv 1 \pmod 2$.
  have L_three_mul_add_two_mod_two {k} : L (3 * k + 2) % 2 = 1 := by
    rw [this, hL2]

  -- Therefore, $L_n$ is even iff $3 \mid n$.
  have L_even_iff {n} : Even (L n) ↔ 3 ∣ n := by
    rw [even_iff, dvd_iff_mod_eq_zero]

    have : n = 3 * (n / 3) + n % 3 := by exact Eq.symm (div_add_mod n 3)
    nth_rw 1 [this]

    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with (hn | hn | hn) <;> rw [hn]
    · rw [add_zero, L_three_mul_mod_two]
    · rw [L_three_mul_add_one_mod_two]
    · rw [L_three_mul_add_two_mod_two]; simp

  -- Therefore, we just need to count the number of $n$ in the interval $[1, 2023]$ such that $n$ is
  -- divisible by $3$.
  let t := {n ∈ Icc 1 2023 | 3 ∣ n}

  suffices t.card = 674 from ?_
  · rw [←this]
    congr
    ext n
    simp [s, t]
    intros
    rw [L_even_iff]


  -- However, we know that this is just $\left\lfloor \frac{2023}{3} \right\rfloor = 674$.
  set_option maxRecDepth 10000 in decide