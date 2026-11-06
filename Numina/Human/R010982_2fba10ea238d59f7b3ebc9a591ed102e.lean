import Mathlib

/-
Let $a_{1}, a_{2}, \ldots$ be an arithmetic sequence and
$b_{1}, b_{2}, \ldots$ be a geometric sequence.
Suppose that $a_{1} b_{1}=20$, $a_{2} b_{2}=19$, and $a_{3} b_{3}=14$.
Find the greatest possible value of $a_{4} b_{4}$.
-/
theorem algebra_609947 (a : ℕ → ℚ) (b : ℕ → ℚ)
    (ha : ∃ c d : ℚ, c ≠ 0 ∧ d ≠ 0 ∧ ∀ n : ℕ, (a n) = c + n*d) -- $a_n$ is arithmetic
    (hb : ∃ e r : ℚ, e ≠ 0 ∧ r ≠ 0 ∧ ∀ n : ℕ, (b n) = e * r^n) -- $b_n$ is geometric
    (h0 : (a 0) * (b 0) = 20) -- Formalization uses zero-indexed sequences
    (h1 : (a 1) * (b 1) = 19)
    (h2 : (a 2) * (b 2) = 14)
  : (a 3) * (b 3) ≤ 37 / 4 := by
  -- Unfold the definitions of arithmetic and geometric sequence.
  obtain ⟨c, d, cnz, dnz, an_eqn⟩ := ha
  obtain ⟨e, r, enz, rnz, bn_eqn⟩ := hb

  -- By using the first equation $a_0b_0 = 20$ we can get $ce = 20$.
  have a0c  : a 0   = c  := by simp [an_eqn 0]
  have b0e  : b 0   = e  := by simp [bn_eqn 0]
  have ce20 : c * e = 20 := by simp [a0c, b0e] at h0; exact h0

  -- Using the second equation $a_1b_1 = 19$ we can get $(c+d)er = 19$.
  have a1 : a 1 = c + d := by simp [an_eqn 1]
  have b1 : b 1 = e * r := by simp [bn_eqn 1]
  have cder19 : (c + d) * (e * r) = 19 := by simp [a1, b1] at h1; exact h1

  -- Now we solve for $c$ in the first, then substitute that into the second.
  have c20e : c = 20 / e := (eq_div_iff_mul_eq enz).mpr ce20

  -- Substitute:
  have eqn1 : (20 / e + d) * (e * r)     = 19 := by rw [c20e] at cder19; exact cder19
  have eqn2 : ((20 / e + d) * e) * r     = 19 := by linarith
  have eqn3 : ((20 / e) * e + d * e) * r = 19 := by linarith
  have eqn4 : (20 + d * e) * r           = 19 := by simp_all
  have eqn5 : 20 * r + d * e * r         = 19 := by linarith
  have eqn6 : d * e * r = 19 - 20 * r         := by linarith

  -- Using the third equation $a_2b_2 = 14$, we obtain a quadratic in $r$.
  -- We eliminate other terms by replacing $(c + d)er = 19$ and $der = 19 - 20r$.
  -- We factor the quadratic and solve for $r$, which gets us two values.
  have a2    : a 2 = c + 2 * d := by simp [an_eqn 2]
  have b2    : b 2 = e * r^2   := by simp [bn_eqn 2]
  have eqn7  : (c + 2 * d) * (e * r^2)   = 14 := by simp [a2, b2] at h2; exact h2
  have eqn8  : (c + d + d) * (e * r) * r = 14 := by linarith
  have eqn9  : ((c+d)*(e*r)+(d*e*r))*r   = 14 := by linarith
  have eqn10 : (19 + (d * e * r)) * r    = 14 := by rw [cder19] at eqn9; exact eqn9
  have eqn11 : (19 + (19 - 20 * r)) * r  = 14 := by rw [eqn6] at eqn10; exact eqn10
  have eqn12 : 38 * r - 20 * r * r       = 14 := by linarith
  have eqn13 : 10 * r * r - 19 * r + 7   = 0  := by linarith -- cancel the 2
  have eqn14 : (2 * r - 1) * (5 * r - 7) = 0  := by linarith -- factor
  have eqn15 : 2 * r - 1 = 0 ∨ 5 * r - 7 = 0  := mul_eq_zero.mp eqn14
  have r_roots : r = 1/2 ∨ r = 7/5            := by
    rcases eqn15 with h | h
    . left ; linarith
    . right; linarith

  -- Now we calculate $a_3b_3$ and use the roots of $r$ and $de$ from above.
  have a3 : a 3 = c + 3 * d := an_eqn 3
  have b3 : b 3 = e * r^3   := bn_eqn 3
  have a3b3 : (a 3) * (b 3) = 57 * r^2 - 40 * r^3 := by
    calc (a 3) * (b 3)
      _ = (c + 3 * d) * (e * r^3)                     := by simp [a3, b3]
      _ = (c + 3 * d) * (e * r) * r^2                 := by linarith
      _ = ((c + d) + 2 * d) * (e * r) * r^2           := by linarith
      _ = ((c + d) * (e * r) + 2 * d * (e * r)) * r^2 := by linarith
      _ = (19 + 2 * (d * e * r)) * r^2                := by rw [cder19]; ring
      _ = (19 + 2 * (19 - 20 * r)) * r^2              := by rw [eqn6]
      _ = (57 - 40 * r) * r^2                         := by linarith
      _ = 57 * r^2 - 40 * r^3                         := by linarith

  -- Using above equation $a_3b_3 = 57r^2 - 40r^3$ and possible values of $r$,
  -- we get the two possible values of $a_3b_3$:
  have possible_values : (a 3) * (b 3) = 37/4 ∨ (a 3) * (b 3) = 49/25 := by
    rcases r_roots with h | h
    . left ; rw [h] at a3b3; group at a3b3; exact a3b3
    . right; rw [h] at a3b3; group at a3b3; exact a3b3

  -- It is easy to show that 49/25 < 37/4, so the max value is 37/4.
  rcases possible_values with h | h <;> linarith
