import Mathlib

/-
Let $N_1$ be a fixed integer and $k$ be a positive integer. Consider the three integers $A = N_1$, $B = N_1 + 4k$, and $C = N_1 + 11k$. Determine the greatest integer that divides $A$, $B$, and $C$ and leaves the same remainder. Show that this integer is $k$.

For verification, let $N_1 = 10$ and $k=3$. The three integers are $A=10$, $B=10+4(3)=22$, $C=10+11(3)=43$.
We are looking for the greatest integer $d$ that divides $10, 22, 43$ and leaves the same remainder $r$.
This integer $d$ must divide the differences:
$B-A = 22-10 = 12$.
$C-B = 43-22 = 21$.
So $d$ must divide $\gcd(12, 21)$.
$\gcd(12, 21) = \gcd(2^2 \cdot 3, 3 \cdot 7) = 3$.
So $d=3$.
The remainder is $r = A \pmod d = 10 \pmod 3 = 1$.
We check:
$10 = 3 \cdot 3 + 1$
$22 = 7 \cdot 3 + 1$
$43 = 14 \cdot 3 + 1$
The remainder is indeed 1 for all numbers. The divisor $d=3$ is greater than the remainder $r=1$.
The result is $3$, which is $k$.
The choice of $N_1$ does not affect the result, as $d = \gcd((N_1+4k)-N_1, (N_1+11k)-(N_1+4k)) = \gcd(4k, 7k) = k \cdot \gcd(4,7) = k \cdot 1 = k$. The remainder will be $N_1 \pmod k$. We need $k > N_1 \pmod k$, which is true unless $N_1 \pmod k = 0$ and $k=0$ (but $k$ is positive) or $k$ is not positive. Since $k$ is a positive integer, $k > N_1 \pmod k$ is always satisfied (as $N_1 \pmod k < k$).
-/

--We prove that if d ∣ 4k and d ∣ 7*k, then d ≤ k, since d has to divide k as well.
lemma l1 (k d:ℤ) (kpos: 0 < k) (hd4: d ∣ (4*k)) (hd7: d ∣ (7*k)):
  d ≤ k := by
  
  have cla : d ∣ k := by 
    have t1 : d ∣ (7*k - 4*k) := by exact Int.dvd_sub hd7 hd4
    have : 7*k - 4*k = 3*k := by ring
    rw [this] at t1
    have t2 : d ∣ (4*k -3*k) := by exact Int.dvd_sub hd4 t1
    have : 4*k - 3*k = k := by ring
    rw [this] at t2
    exact t2

  exact Int.le_of_dvd kpos cla

theorem number_theory_635195 (N1 k A B C: ℤ) (kpos: 0 < k) (hA: A = N1) (hB: B = N1 + 4*k) (hC: C = N1 + 11*k):
  IsGreatest {d:ℤ | A % d = B % d ∧ B % d = C % d} k := by

  unfold IsGreatest upperBounds
  simp

  constructor

  -- k is valid by simple verfication.
  simp [hA, hB, hC]

  -- prove there's no larger one.
  intro d adbd bdcd

  simp [hA,hB,hC] at adbd bdcd

  --For every such d, we have d ∣ 4k and d ∣ 7k, so by the lemma, we have d ≤ k.
  have t1: d ∣ (4*k) := by 
    have l: d ∣ N1 + 4*k - N1 := by exact Int.ModEq.dvd adbd
    have : N1 + 4*k - N1 = 4*k := by ring
    rw [this] at l
    exact l
  have t2: d ∣ (7*k) := by 
    have l: d ∣ N1 + 11*k - (N1 + 4*k) := by exact Int.ModEq.dvd bdcd
    have : N1 + 11*k - (N1 + 4*k) = 7*k := by ring
    rw [this] at l
    exact l

  apply l1
  exact kpos
  exact t1
  exact t2