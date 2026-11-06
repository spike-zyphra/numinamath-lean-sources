import Mathlib

namespace number_theory_640148

lemma eq_0_of_all_nonzero_dvd (b : ℤ) (h : ∀ a ≠ 0, a ∣ b) : b = 0 := by
  by_contra
  have : 2 * b ∣ b :=
    h (2 * b) (by omega)
  rcases this with ⟨c, eq⟩
  have : b = 0 := by
    have mul_eq_0 : b * (2 * c - 1) = 0 := by
      linarith
    have right_ne_0 : 2 * c - 1 ≠ 0 := by
      omega
    simp [right_ne_0] at mul_eq_0
    exact mul_eq_0
  contradiction

theorem number_theory_640148 {P : Polynomial ℤ} {a b : ℕ} (h : ∀ k ≠ b, (b - k : ℤ) ∣ (a - P.eval (k : ℤ))) : a = P.eval (b : ℤ) := by
  --  1. Let $C = a-P(b)$. Since $a \in \mathbb{N}$ and $P(x) \in \mathbb{Z}[x]$, $P(b)$ is an integer, so $C$ is an integer.
  let C := a - P.eval (b : ℤ)
  --  2. It is a known property of polynomials with integer coefficients that for any distinct integers $x$ and $y$, $x-y$ divides $P(x)-P(y)$.
  --  3. Applying this property with $x=b$ and $y=k$ (where $k \in \mathbb{N}, k \neq b$), we have $b-k \mid P(b)-P(k)$.
  have (k) : (b - k : ℤ) ∣ P.eval (b : ℤ) - P.eval (k : ℤ) := by
    exact Polynomial.sub_dvd_eval_sub (↑b) k P
  --  4. The given condition is $b-k \mid a-P(k)$ for all $k \in \mathbb{N}, k \neq b$.
  /-
   5. Since $b-k$ divides $a-P(k)$ and $b-k$ divides $P(b)-P(k)$, it must divide their difference:\
      $b-k \mid (a-P(k)) - (P(b)-P(k))$.\
      $(a-P(k)) - (P(b)-P(k)) = a-P(k)-P(b)+P(k) = a-P(b)$.\
      So, $b-k \mid a-P(b)$.
  -/
  --  6. This means $b-k \mid C$ for all $k \in \mathbb{N}, k \neq b$.
  have : ∀ k ≠ b, (b - k : ℤ) ∣ C := by
    intro k k_ne_b
    unfold C
    specialize this k
    specialize h k k_ne_b
    have := Int.dvd_sub h this
    convert this using 1
    ring
  --  7. The set of integers $S_D = \{b-k \mid k \in \mathbb{N}, k \neq b\}$ is an infinite set. For example, for $k > b$, $b-k$ can take values $-1, -2, -3, \dots$ by choosing $k=b+1, b+2, b+3, \dots$ respectively. All these values must divide $C$.
  have : ∀ i ≠ 0, i ∣ C := by
    intro i i_ne_0
    wlog i_neg : i < 0 generalizing i
    . specialize this (-i) (by omega) (by omega)
      exact Int.neg_dvd.mp this
    specialize this (b - i).toNat (by omega)
    convert this
    . omega
  --  8. An integer $C$ has infinitely many distinct divisors if and only if $C=0$. If $C \neq 0$, then any divisor $d$ of $C$ must satisfy $|d| \le |C|$. This means a non-zero integer has a finite number of divisors.
  --  9. Since $C$ must be divisible by all integers in the infinite set $S_D$, $C$ must have infinitely many divisors. Therefore, $C=0$.
  have : C = 0 := by
    exact eq_0_of_all_nonzero_dvd C this
  -- 10. From $C=0$, we have $a-P(b)=0$, which implies $a=P(b)$.
  unfold C at this
  linarith

end number_theory_640148
open number_theory_640148
