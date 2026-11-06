import Mathlib

open Polynomial

/- On a faded piece of paper it is possible, with some effort, to discern the following:

$$
\left(x^{2}+x+a\right)\left(x^{15}-\ldots\right)=x^{17}+x^{13}+x^{5}-90 x^{4}+x-90
$$

Some parts have got lost, partly the constant term of the first factor of the left side, partly the main part of the other factor. It would be possible to restore the polynomial forming the other factor, but we restrict ourselves to asking the question: What is the value of the constant term a? We assume that all polynomials in the statement above have only integer coefficients. -/
theorem algebra_608003 {a : ℤ} (h : ∃ S : ℤ[X], (X^2 + X + (a: ℤ[X])) * (X^15 - S) = X^17 + X^13 + X^5 - 90*X^4 + X - 90) :
    a = 2 := by
  -- We denote the polynomial $x^{2}+x+a$ by $P_{a}(x)$, the polynomial forming the other factor of the left side by $Q(x)$ and the polynomial on the right side by $R(x)$.
  let P := X^2 + X + (a : ℤ[X])
  rcases h with ⟨S, h_eq⟩
  let Q := P * (X^15 - S)
  let R : ℤ[X] := X^17 + X^13 + X^5 - 90*X^4 + X - 90
  -- The polynomials are integer valued for every integer $x$.
  let p x : ℤ := x^2 + x + a
  let r x : ℤ := x^17 + x^13 + x^5 - 90*x^4 + x - 90
  have p_dvd_r x : p x ∣ r x := by
    have p_eq_P_eval: p x = P.eval x := by unfold p P; simp
    have r_eq_R_eval: r x = R.eval x := by unfold r R; simp
    rw [p_eq_P_eval, r_eq_R_eval]
    have P_dvd_R : P ∣ R := Dvd.intro (X ^ 15 - S) h_eq
    exact eval_dvd P_dvd_R
  -- For $x=0$ we get $P_{a}(0)=a$ and $R(0)=-90$, so $a$ is a divisor of $90=2 \cdot 3 \cdot 3 \cdot 5$.
  have a_dvd_90 : a ∣ 90 := by
    have : a ∣ -90 := by
      have p_0_eq : p 0 = a := by unfold p; simp
      have r_0_eq : r 0 = -90 := by unfold r; rfl
      rw [← p_0_eq, ← r_0_eq]
      exact p_dvd_r 0
    exact Int.dvd_neg.mp this
  -- For $x=-1$ we get $P_{a}(-1)=-184$, so $a$ is also a divisor of $184=2 \cdot 2 \cdot 2 \cdot 23$.
  have a_dvd_184 : a ∣ 184 := by
    have : a ∣ -184 := by
      have p_m_1_eq : p (-1) = a := by unfold p; simp
      have r_m_1_eq : r (-1) = -184 := by unfold r; rfl
      rw [← p_m_1_eq, ← r_m_1_eq]
      exact p_dvd_r (-1)
    exact Int.dvd_neg.mp this
  -- But the only prime factor in common is 2 .
  have a_dvd_2 : a ∣ 2 :=
    dvd_gcd a_dvd_90 a_dvd_184
  -- So the only possibilities for $a$ are $\pm 2$ and $\pm 1$.
  have a_in : a ∈ ({-2, -1, 1 ,2} : Finset ℤ) := by
    -- There is no `Int.divisors`.
    let abs := a.natAbs
    have abs_in_divisors : abs ∈ ({1, 2} : Finset ℕ) := by
      rw [show {1, 2} = (2 : ℕ).divisors from rfl]
      have : abs ∣ 2 := Int.ofNat_dvd_right.mp a_dvd_2
      exact Nat.mem_divisors.mpr ⟨this, by simp⟩
    simp
    suffices (a = -2 ∨ a = -1) ∨ (a = 1 ∨ a = 2) by tauto
    simp at abs_in_divisors
    rcases Int.natAbs_eq a with a_eq | a_eq
    . right
      rw [a_eq]
      rcases abs_in_divisors with abs_eq | abs_eq
      . left
        norm_cast
      . right
        norm_cast
    . left
      rw [show a.natAbs = abs from rfl] at a_eq
      rcases abs_in_divisors with abs_eq | abs_eq
      . right
        rw [abs_eq] at a_eq
        exact a_eq
      . left
        rw [abs_eq] at a_eq
        exact a_eq

  have p_1_dvd_minus_176 : p 1 ∣ -176 := by
    convert p_dvd_r 1 using 1
  fin_cases a_in
  . -- If $a=-2$ we get for $x=1$ that $P_{2}(1)=0$, i.e. the left side is equal to 0 , while the right side is equal to $R(1)=-176$, which is different from 0 .
    exfalso
    unfold p at p_1_dvd_minus_176
    ring_nf at p_1_dvd_minus_176
    contradiction
  . --  Before we use the procedure above again, we need a factorization of $R(x)$. We observe that $x^{4}+1$ is a divisor of $R(x)$, since the right side may be written as $\left(x^{4}+1\right)\left(x^{13}+x-90\right)$. If $a=-1$ we get for $x=2$ that $P_{1}(2)=5$, while $x^{4}+1=17$ and $x^{13}+x-90=8104$. So the right hand side is not divisible by 5 .
    exfalso
    have := p_dvd_r 2
    -- not needed with brute force computing
    --have r_eq x : r x = (x^4 + 1) * (x^13 + x - 90) := by ring
    unfold p r at this
    ring_nf at this
    contradiction
  . -- If $a=1$, we get for $x=1$ that $P_{1}(1)=3$, while $R(1)=4-180=-176$, which cannot be divided by 3 .
    exfalso
    unfold p at p_1_dvd_minus_176
    ring_nf at p_1_dvd_minus_176
    contradiction
  . -- Now, the only remaining possibility is $a=2$, i.e. $x^{2}+x+2$ is a divisor of $R(x)$.
    rfl
