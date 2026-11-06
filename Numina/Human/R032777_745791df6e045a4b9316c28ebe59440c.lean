import Mathlib

open Complex

/-- There are real numbers $a, b, c,$ and $d$ such that $-20$ is a root of $x^3 + ax + b$ and $-21$
is a root of $x^3 + cx^2 + d.$ These two polynomials share a complex root $m + \sqrt{n} \cdot i,$
where $m$ and $n$ are positive integers and $i = \sqrt{-1}.$ Find $m+n.$ -/
theorem algebra_98574 (a b c d : ℝ) (m n : ℕ) (_ : m > 0) (hn : n > 0)
    (h1 : (-20)^3 + a * (-20) + b = 0) (h2 : (-21)^3 + c * (-21)^2 + d = 0)
    (h3 : (m+ √n * Complex.I)^3 + a * (m + √n * Complex.I) + b = 0)
    (h4 : (m + √n * Complex.I)^3 + c * (m + √n * Complex.I)^2 + d = 0) :
    m + n = 330 := by

  -- Let's analyze the polynomials $p(x) = x^3 + ax + b$ and $q(x) = x^3 + cx^2 + d$.
  let p := Cubic.mk (R := ℂ) 1 0 a b
  let q := Cubic.mk (R := ℂ) 1 c 0 d

  -- Let's start with $p$. Obviously, $p$ is a nonzero polynomials.
  have p_toPoly_ne_zero : p.toPoly ≠ 0 := by
    apply Cubic.ne_zero_of_a_ne_zero
    simp [p]

  -- We claim that the roots of $p$ are $-20$, $m + \sqrt{n}i$, and $m - \sqrt{n}i$. #-20$ and
  -- $m + \sqrt{n}i$ are roots of $p$ by assumption. Because $p$ is a real polynomial, the complex
  -- conjugate of $m + \sqrt{n}i$, which is $m - \sqrt{n}i$, is also a root of $p$. Moreover, a
  -- polynomial of degree $3$ has at most $3$ roots. Therefore, the roots of $p$ are precisely
  -- $-20$, $m + \sqrt{n}i$, and $m - \sqrt{n}i$.
  have p_roots_eq : p.roots = {-20, m + √n * I, m - √n * I} := by
    symm
    apply Multiset.eq_of_le_of_card_le
    · simp only [Multiset.insert_eq_cons]
      rw [Multiset.cons_le_of_not_mem, Multiset.cons_le_of_not_mem, Multiset.singleton_le]
      · refine ⟨?_, ?_, ?_⟩
        <;> simp [Cubic.mem_roots_iff p_toPoly_ne_zero, p]
        · convert h1
          norm_cast
          norm_num
        · exact h3
        · rw [←star_inj, star_zero]
          simp [p]
          exact h3
      · simp only [Multiset.mem_singleton]
        intro h
        suffices n = 0 from by omega
        suffices √n * I = 0 from by simpa
        calc _ = (m + √n * I - m + √n * I) / 2 := by simp
             _ = (m - √n * I - m + √n * I) / 2 := by rw [h]
             _ = 0 := by simp
      · simp only [Multiset.mem_cons, Multiset.mem_singleton]
        rintro (h | h)
        · suffices n = 0 from by omega
          suffices √n = 0 from by simpa
          calc _ = im (m + √n * I) := by simp
               _ = im (-20) := by rw [h]
               _ = 0 := by simp
        · suffices n = 0 from by omega
          suffices -√n = 0 from by simpa
          calc _ = im (m - √n * I) := by simp
               _ = im (-20) := by rw [h]
               _ = 0 := by simp
    · simp [Cubic.roots]
      convert Polynomial.card_roots' p.toPoly
      apply (Cubic.natDegree_of_a_ne_zero (by simp [p])).symm

  -- Now, let's analyze the polynomial $q$. Obviously, $q$ is a nonzero polynomial.
  have q_toPoly_ne_zero : q.toPoly ≠ 0 := by
    apply Cubic.ne_zero_of_a_ne_zero
    simp [q]

  -- We claim that the roots of $q$ are $-21$, $m + \sqrt{n}i$, and $m - \sqrt{n}i$. $-21$ and
  -- $m + \sqrt{n}i$ are roots of $q$ by assumption. Because $q$ is a real polynomial, the complex
  -- conjugate of $m + \sqrt{n}i$, which is $m - \sqrt{n}i$, is also a root of $q$. Moreover, a
  -- polynomial of degree $3$ has at most $3$ roots. Therefore, the roots of $q$ are precisely
  -- $-21$, $m + \sqrt{n}i$, and $m - \sqrt{n}i$.
  have q_roots_eq : q.roots = {-21, m + √n * I, m - √n * I} := by
    symm
    apply Multiset.eq_of_le_of_card_le
    · simp only [Multiset.insert_eq_cons]
      rw [Multiset.cons_le_of_not_mem, Multiset.cons_le_of_not_mem, Multiset.singleton_le]
      · refine ⟨?_, ?_, ?_⟩
        <;> simp [Cubic.mem_roots_iff q_toPoly_ne_zero, q]
        · convert h2
          norm_cast
        · exact h4
        · rw [←star_inj, star_zero]
          simp [q]
          exact h4
      · simp only [Multiset.mem_singleton]
        intro h
        suffices n = 0 from by omega
        suffices √n * I = 0 from by simpa
        calc _ = (m + √n * I - m + √n * I) / 2 := by simp
             _ = (m - √n * I - m + √n * I) / 2 := by rw [h]
             _ = 0 := by simp
      · simp only [Multiset.mem_cons, Multiset.mem_singleton]
        rintro (h | h)
        · suffices n = 0 from by omega
          suffices √n = 0 from by simpa
          calc _ = im (m + √n * I) := by simp
               _ = im (-21) := by rw [h]
               _ = 0 := by simp
        · suffices n = 0 from by omega
          suffices -√n = 0 from by simpa
          calc _ = im (m - √n * I) := by simp
               _ = im (-21) := by rw [h]
               _ = 0 := by simp
    · simp [Cubic.roots]
      convert Polynomial.card_roots' q.toPoly
      apply (Cubic.natDegree_of_a_ne_zero (by simp [q])).symm

  -- Now, we have all the information we need to solve the problem. We claim that $m = 10$ and
  -- $n = 320$.
  suffices (m : ℂ) = 10 ∧ ((m : ℂ) = 10 → (n : ℂ) = 320) from by norm_cast at this; omega
  refine ⟨?_, ?_⟩

  -- Let's first show that $m = 10$. This follows from Vieta's formula for the polynomial $p$
  -- corresponding to the $x^2$ coefficient which is $0$.
  · have : 0 = -20 + (m + √n * I) + (m - √n * I) := by
      suffices (-1) * 0 = (-1) * (-20 + (m + √n * I) + (m - √n * I)) from by rwa [mul_right_inj' (by norm_num)] at this
      convert Cubic.b_eq_three_roots (φ := RingHom.id ℂ) (P := p) (by simp [p]) p_roots_eq using 1
      · simp [p]
      · simp

    calc _ = (2 * (m : ℂ)) / 2 := by simp
         _ = (m + m) / 2 := by simp
         _ = ((m + √n * I) + (m - √n * I)) / 2 := by simp
         _ = (20 + ((-20) + (m + √n * I) + (m - √n * I))) / 2 := by ring
         _ = (20 + 0) / 2 := by congr; exact this.symm
         _ = _ := by norm_num

  -- Now, let's show that $n = 320$. This follows from Vieta's formula for the polynomial $q$
  -- corresponding to the $x$ coefficient which is $0$, and from the fact that $m = 10$.
  · intro hm

    have : 0 = (-21) * (10 + √n * I) + (-21) * (10 - √n * I) + (10 + √n * I) * (10 - √n * I) := by
      rw [←hm]
      convert Cubic.c_eq_three_roots (φ := RingHom.id ℂ) (P := q) (by simp [q]) q_roots_eq using 1
      simp

    have : (0:ℂ) = -320 + n := by
      convert Cubic.c_eq_three_roots (φ := RingHom.id ℂ) (P := q) (by simp [q]) q_roots_eq using 1
      rw [hm]
      ring_nf
      simp
      norm_cast
      convert (Real.sq_sqrt _).symm
      norm_cast
      apply zero_le

    calc _ = (-320 + (n : ℂ)) + 320 := by ring
         _ = 320 := by rw [←this, zero_add]