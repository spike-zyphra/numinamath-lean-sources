import Mathlib

/-
16. (KOR 2) Prove that $N=\frac{5^{125}-1}{5^{25}-1}$ is a composite number.
-/
theorem Other_3764 :
  ∃ x₁ y, x₁ ≠ 1 ∧ y ≠ 1 ∧ x₁ * y = (((5 ^ (125 : ℕ) - 1) / (5 ^ (25 : ℕ) - 1)) : ℕ) := by

/- 16. Observe that $x^{4}+x^{3}+x^{2}+x+1=\left(x^{2}+3 x+1\right)^{2}-5 x(x+1)^{2}$. -/
  let x := 5 ^ 25
  let N := ((5 ^ 125 - 1) / (5 ^ 25 - 1) : ℕ)
  have xdef : x = 5 ^ 25 := rfl
  have Ndef : N = (5 ^ 125 - 1) / (5 ^ 25 - 1) := rfl
  have hN : N = x^4 + x^3 + x^2 + x + 1 := by
    rw [Ndef, xdef]; ring

/- Thus for $x=5^{25}$ we have  $$ \begin{aligned} N & =x^{4}+x^{3}+x^{2}+x+1 \\ & =\left(x^{2}+3 x+1-5^{13}(x+1)\right)\left(x^{2}+3 x+1+5^{13}(x+1)\right)=A \cdot B . \end{aligned} $$  -/
  have fac : x^4 + x^3 + x^2 + x + 1 =
    ((x^2 + 3*x + 1) - 5^13*(x+1)) * ((x^2 + 3*x + 1) + 5^13*(x+1)) := by ring
  rw [← Ndef, hN, fac]
  let A := (x^2 + 3*x + 1) - 5^13*(x+1);
  let B := (x^2 + 3*x + 1) + 5^13*(x+1);
  have Adef : A = (x^2 + 3*x + 1) - 5^13*(x+1) := rfl
  have Bdef : B = (x^2 + 3*x + 1) + 5^13*(x+1) := rfl

/- Clearly, both $A$ and $B$ are positive integers greater than 1. -/
  have Apos : 1 < A := by
    rw [Adef]
    ring_nf
    linarith
  have Bpos : 1 < B := by 
    rw [Bdef]
    ring_nf
    omega
  exact ⟨A, B, Nat.ne_of_gt Apos, Nat.ne_of_gt Bpos, rfl⟩