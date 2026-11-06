import Mathlib
/- Example 1 Let $a, b, c, d, e$ be positive numbers, satisfying $a b c d e=1$. Prove:
$$
\sum \frac{a+a b c}{1+a b+a b c d} \geqslant \frac{10}{3},
$$

where, “$\sum$” denotes the cyclic sum. -/
theorem number_theory_117356 (a b c d e : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (he : e > 0) (h : a * b * c * d * e = 1) : (a + a * b * c) / (1 + a * b + a * b * c * d) + (b + b * c * d) / (1 + b * c + b * c * d * e) + (c + c * d * e) / (1 + c * d + c * d * e * a) + (d + d * e * a) / (1 + d * e + d * e * a * b) + (e + e * a * b) / (1 + e * a + e * a * b * c) ≥ 10 / 3:= by
  -- Define variables x1 through x5 to simplify the expressions
  set x1:= (1 : ℝ) with hx1
  rw [hx1]
  set x2:= a with hx2
  set x3:= a * b with hx3
  set x4:= a * b * c with hx4
  set x5:= a * b * c * d with hx5
  clear_value x1 x2 x3 x4 x5
  rw [hx2] at ha ⊢
  rw [show 1 + x3 + x5 = x1 + x3 + x5 by rw [hx1]]

  -- Express a, b, c, d, e in terms of the new variables x1 through x5
  have g1 : a = x2 / x1:= by
    subst x1 x2
    simp
  have g2 : b = x3 / x2:= by
    subst x3 x2
    field_simp
  have g3 : c = x4 / x3:= by
    subst x4 x3
    field_simp
  have g4 : d = x5 / x4:= by
    subst x5 x4
    field_simp
  have g5 : e = x1 / x5:= by
    subst x1 x5
    field_simp
    linarith
  rw [show a + x4 = x2 + x4 by rw [hx2]]

  -- Establish that all x variables are positive
  replace hx1 : x1 > 0:= by
    subst x1
    positivity
  replace hx2 : x2 > 0:= by
    subst x2
    positivity
  replace hx3 : x3 > 0:= by
    subst x3
    positivity
  replace hx4 : x4 > 0:= by
    subst x4
    positivity
  replace hx5 : x5 > 0:= by
    subst x5
    positivity

  -- Rewrite each term of the cyclic sum using the x variables
  rw [show (b + b * c * d) / (1 + b * c + b * c * d * e) = (x3 + x5) / (x2 + x4 + x1) by subst a b c d e ; field_simp ; ring_nf]
  rw [show (c + c * d * e) / (1 + c * d + c * d * e * a) = (x4 + x1) / (x3 + x5 + x2) by subst a b c d e ; field_simp ; ring_nf]
  rw [show (d + d * e * a) / (1 + d * e + d * e * a * b) = (x5 + x2) / (x4 + x1 + x3) by subst a b c d e ; field_simp ; ring_nf]
  rw [show (e + e * a * b) / (1 + e * a + e * a * b * c) = (x1 + x3) / (x5 + x2 + x4) by subst a b c d e ; field_simp ; ring_nf]
  clear g1 g2 g3 g4 g5 ha hb hc hd he h a b c d e

  -- Transform each fraction to prepare for applying Cauchy-Schwarz inequality
  rw [show (x2 + x4) / (x1 + x3 + x5) = (x1 + x2 + x3 + x4 + x5) * (1 / (x1 + x3 + x5)) - 1 by field_simp ; ring_nf]
  rw [show (x3 + x5) / (x2 + x4 + x1) = (x1 + x2 + x3 + x4 + x5) * (1 / (x2 + x4 + x1)) - 1 by field_simp ; ring_nf]
  rw [show (x4 + x1) / (x3 + x5 + x2) = (x1 + x2 + x3 + x4 + x5) * (1 / (x3 + x5 + x2)) - 1 by field_simp ; ring_nf]
  rw [show (x5 + x2) / (x4 + x1 + x3) = (x1 + x2 + x3 + x4 + x5) * (1 / (x4 + x1 + x3)) - 1 by field_simp ; ring_nf]
  rw [show (x1 + x3) / (x5 + x2 + x4) = (x1 + x2 + x3 + x4 + x5) * (1 / (x5 + x2 + x4)) - 1 by field_simp ; ring_nf]

  -- Simplify the goal to focus on the sum of reciprocals
  suffices (x1 + x2 + x3 + x4 + x5) * (1 / (x1 + x3 + x5) + 1 / (x2 + x4 + x1) + 1 / (x3 + x5 + x2) + 1 / (x4 + x1 + x3) + 1 / (x5 + x2 + x4)) ≥ 25 / 3 by linarith

  -- Define functions f and g for applying Cauchy-Schwarz inequality
  set f : ℕ → ℝ:= fun i => if i = 0 then √(x1 + x3 + x5) else if i = 1 then √(x2 + x4 + x1) else if i = 2 then √(x3 + x5 + x2) else if i = 3 then √(x4 + x1 + x3) else √(x5 + x2 + x4) with hf
  set g : ℕ → ℝ:= fun i => if i = 0 then 1 / √(x1 + x3 + x5) else if i = 1 then 1 / √(x2 + x4 + x1) else if i = 2 then 1 / √(x3 + x5 + x2) else if i = 3 then 1 / √(x4 + x1 + x3) else 1 / √(x5 + x2 + x4) with hg

  -- Apply Cauchy-Schwarz inequality
  have h : (∑ i ∈ Finset.range 5, f i * g i) ^ 2 ≤ (∑ i ∈ Finset.range 5, f i ^ 2) * ∑ i ∈ Finset.range 5, g i ^ 2:= by exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.range 5) f g

  -- Calculate the sum of f*g, which equals 5
  have h1 : ∑ i ∈ Finset.range 5, f i * g i = 5:= by
    simp [Finset.sum_range_succ, hf, hg]
    field_simp
    linarith

  -- Calculate the sum of f^2, which equals 3*(sum of all x variables)
  have h2 : ∑ i ∈ Finset.range 5, f i ^ 2 = 3 * (x1 + x2 + x3 + x4 + x5):= by
    simp [Finset.sum_range_succ, hf]
    field_simp
    linarith

  -- Calculate the sum of g^2, which equals the sum of reciprocals we need
  have h3 : ∑ i ∈ Finset.range 5, g i ^ 2 = 1 / (x1 + x3 + x5) + 1 / (x2 + x4 + x1) + 1 / (x3 + x5 + x2) + 1 / (x4 + x1 + x3) + 1 / (x5 + x2 + x4):= by
    simp [Finset.sum_range_succ, hg]
    field_simp

  -- Combine the results to complete the proof
  rw [h1, h2, h3] at h
  linarith
