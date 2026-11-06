import Mathlib

open Nat

/-- Find the number of $7$-tuples of positive integers $(a,b,c,d,e,f,g)$ that satisfy the following
systems of equations: \begin{align*} abc&=70,\\ cde&=71,\\ efg&=72. \end{align*} -/
theorem number_theory_97969 :
    {(a, b, c, d, e, f, g) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ |
    a * b * c = 70 ∧
    c * d * e = 71 ∧
    e * f * g = 72}.ncard = 96 := by

  -- Let $p$ be the set of $7$-tuples of positive integers $(a,b,c,d,e,f,g)$ that satisfy the given
  -- system of equations.
  set p := {(a, b, c, d, e, f, g) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ |
    a * b * c = 70 ∧
    c * d * e = 71 ∧
    e * f * g = 72}

  -- Let $q$ be the set of pairs $(x, y)$ of positive integers such that $x | 70$ and $y | 72$.
  set q := (divisors 70) ×ˢ (divisors 72)

  -- We claim that the number of elements of $p$ is 96. To that end, it is enough to show that $p$
  -- and $q$ have the same number of elements because $q$ has 96 elements as $70 = 2 * 5 * 7$ has
  -- $2 * 2 * 2 = 8$ divisors and $72 = 2^3 * 3^2$ has $4 * 3 = 12$ divisors.
  suffices q.card = p.ncard from by rw [←this]; decide
  rw [←Set.ncard_coe_Finset]

  -- We claim that the function $(a, f) \mapsto (a, 70/a, 1, 71, 1, f, 72/f)$ is a bijection between
  -- $q$ and $p$.
  apply Set.ncard_congr (fun (a, f) _ ↦ ⟨a, 70/a, 1, 71, 1, f, 72/f⟩)

  -- Given $(a, f) \in q$, the tuple $(a, 70/a, 1, 71, 1, f, 72/f)$ clearly satisfies the given
  -- system of equations so the function maps $q$ into $p$.
  · rintro ⟨a, f⟩ h
    simp [p, q] at h ⊢
    constructor
    · rw [Nat.mul_div_cancel' h.1]
    · rw [Nat.mul_div_cancel' h.2]

  -- Now, let's show that the function is injective. Let $(a_1, f_1)$ and $(a_2, f_2)$ be two pairs
  -- such that $(a_1, 70/a_1, 1, 71, 1, f_1, 72/f_1) = (a_2, 70/a_2, 1, 71, 1, f_2, 72/f_2)$. The
  -- first and last components of the tuples give back the inputs, so $a_1 = a_2$ and $f_1 = f_2$
  -- showing that the function is injective.
  · rintro ⟨a1, f1⟩ ⟨a2, f2⟩ h1 h2 h3
    simp [p, q] at h1 h2 h3 ⊢
    exact ⟨h3.1, h3.2.2.1⟩

  -- Lastly, let's show that the function is surjective. Let $(a, b, c, d, e, f, g) \in p$.
  · rintro ⟨a, b, c, d, e, f, g⟩ ⟨h1, h2, h3⟩

    -- We claim that $(a, f)$ is in $q$ and hits the tuple $(a, b, c, d, e, f, g)$. To that end,
    -- it is enough to show that $a | 70$, $f | 72$ and
    -- $(a, 70/a, 1, 71, 1, f, 72/f) = (a, b, c, d, e, f, g)$.
    simp [q]

    -- First, observe that $c$ divides $70$ because of the equation $abc = 70$ and divides $71$
    -- because of the equation $cde = 71$. Therefore, $c | \operatorname{gcd}(70, 71) = 1$ so $c = 1$.
    have hc : c = 1 := by
      rw [←dvd_one]
      show c ∣ Nat.gcd 70 71
      apply Nat.dvd_gcd
      · use a * b
        convert h1.symm using 1
        ring
      · use d * e
        convert h2.symm using 1
        ring

    -- Similarly, $e$ divides $71$ because of the equation $cde = 71$ and divides $72$ because of
    -- the equation $efg = 72$. Therefore, $e | \operatorname{gcd}(71, 72) = 1$ so $e = 1$.
    have he : e = 1 := by
      rw [←dvd_one]
      show e ∣ Nat.gcd 71 72
      apply Nat.dvd_gcd
      · use c * d
        convert h2.symm using 1
        ring
      · use f * g
        convert h3.symm using 1
        ring

    -- Then, from the equation $cde = 71$, we get $d = 71$.
    have hd : d = 71 := by
      calc _ = c * d * e := by rw [hc, he, one_mul, mul_one]
           _ = 71 := by rw [h2]

    subst hc he hd
    simp at h1 h2 h3 ⊢; clear h2

    -- The rest is showing that $a | 70$ and $f | 72$. But these are immediate from the equations
    -- $abc = 70$ and $efg = 72$.
    refine ⟨?_, ⟨⟨b, h1.symm⟩, g, h3.symm⟩, ?_⟩
    · calc _ = (a * b) / a := by rw [h1]
           _ = _ := by simp [(by nlinarith : a ≠ 0)]
    · calc _ = (f * g) / f := by rw [←h3]
           _ = _ := by simp [(by nlinarith : f ≠ 0)]