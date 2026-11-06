import Mathlib

open Polynomial

/- Prove that if


$$

\frac{1}{a}+\frac{1}{b}+\frac{1}{c}=\frac{1}{a+b+c}

$$


and $n$ is a positive odd number, then


$$

\frac{1}{a^{n}}+\frac{1}{b^{n}}+\frac{1}{c^{n}}=\frac{1}{a^{n}+b^{n}+c^{n}}

$$
 -/
theorem algebra_231721 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (habc : a + b + c ≠ 0)
  (h : 1 / a + 1 / b + 1 / c = 1 / (a + b + c)) (n : ℕ) (hn : Odd n) :
    1 / a ^ n + 1 / b ^ n + 1 / c ^ n = 1 / (a ^ n + b ^ n + c ^ n)
  := by
    -- ab ≠ 0
    have hab : a * b ≠ 0 := (mul_ne_zero_iff_right hb).mpr ha

    -- combine fractions
    have common : (a * b + b * c + c * a) / (a * b * c) = 1 / (a + b + c) := by
      rw [div_add_div _ _ ha hb] at h
      rw [div_add_div _ _ hab hc] at h
      convert h using 2
      ring

    -- abc ≠ 0
    have mul_abc : a * b * c ≠ 0 := (mul_ne_zero_iff_right hc).mpr hab

    -- rewrite as (a * b + b * c + c * a) * (a + b + c) = a * b * c
    have as_mul := (div_eq_div_iff mul_abc habc).mp common
    rw [one_mul] at as_mul

    -- consider the polynomial (x - a) * (x - b) * (x - c)
    let F : ℝ[X] := (X - C a) * (X - C b) * (X - C c)

    -- it's roots are a, b, c
    have F_roots : F.roots = {a, b, c} := by
      -- the polynomials are non-zero
      have a_ne_zero := X_sub_C_ne_zero a
      have b_ne_zero := X_sub_C_ne_zero b
      have c_ne_zero := X_sub_C_ne_zero c
      have a_b_ne_zero := mul_ne_zero a_ne_zero b_ne_zero
      have a_b_c_ne_zero := mul_ne_zero a_b_ne_zero c_ne_zero

      -- then we know the roots of each factor
      simp only [Polynomial.roots_mul a_b_c_ne_zero, Polynomial.roots_mul a_b_ne_zero,
        Polynomial.roots_X_sub_C, Multiset.singleton_add, Multiset.cons_add,
        Multiset.insert_eq_cons]

    -- consider the polynomial (x - (a + b + c)) * (x ^ 2 + (a * b + b * c + c * a))
    let G : ℝ[X] := (X - C (a + b + c)) * (X ^ 2 + C (a * b + b * c + c * a))

    -- a + b + c is a root
    have G_roots_mem : a + b + c ∈ G.roots := by
      -- factors are non-zero
      have left_ne_zero := X_sub_C_ne_zero (a + b + c)
      have right_ne_zero : (X ^ 2 + C (a * b + b * c + c * a)) ≠ 0 := by
        have pos : 0 < 2 := by omega
        exact Polynomial.X_pow_add_C_ne_zero pos _
      have ne_zero := mul_ne_zero left_ne_zero right_ne_zero

      -- a + b + c is a root of a polynomial if it's the root of one of the factors
      rw [Polynomial.roots_mul ne_zero, Multiset.mem_add]

      -- it's a root of the left factor
      refine Or.inl ?_
      rw [Polynomial.roots_X_sub_C]
      exact Multiset.mem_singleton.mpr rfl

    -- the two polynomials are equal
    have F_eq_G : F = G := by
      apply Polynomial.funext
      intro x
      unfold F G
      simp only [eval_mul, eval_sub, eval_X, eval_C, map_add, map_mul, eval_add, eval_pow]
      calc (x - a) * (x - b) * (x - c)
      _ = x ^ 3 - (a + b + c) * x ^ 2 + (a * b + b * c + c * a) * x - a * b * c := by ring
      _ = x ^ 3 - (a + b + c) * x ^ 2 + (a * b + b * c + c * a) * x - ((a * b + b * c + c * a) * (a + b + c)) := by rw [←as_mul]
      _ = _ := by ring

    -- so we have that a + b + c = a or b or c
    rw [←F_eq_G, F_roots] at G_roots_mem
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at G_roots_mem

    -- if we have such an equality as x + y + z = z, then 1 / x ^ n + 1 / y ^ n + 1 / z ^ n = 1 / (x ^ n + y ^ n + z ^ n)
    have general : ∀ {x y z : ℝ}, x + y + z = z
      → 1 / x ^ n + 1 / y ^ n + 1 / z ^ n = 1 / (x ^ n + y ^ n + z ^ n)
      := by
        intro x y z h
        have x_eq : x = -y := by linarith
        -- odd power of negative number is negative
        have pow_eq : (-y) ^ n = -(y ^ n) := Odd.neg_pow hn _
        rw [x_eq, pow_eq]
        ring

    -- it covers all three cases of the equality of a + b + c
    rcases G_roots_mem with h1 | h2 | h3
    -- a + b + c = a ↔ c + b + a = a
    · convert_to c + b + a = a at h1
      · ring
      convert general h1 using 1 <;> ring
    -- a + b + c = b ↔ a + c + b = b
    · convert_to a + c + b = b at h2
      · ring
      convert general h2 using 1 <;> ring
    · exact general h3