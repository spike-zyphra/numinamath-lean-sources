import Mathlib

/-
Let's prove that if $n$ is a natural number,
then the integer part of the following number is not a perfect square:

$$
\frac{2 \sqrt{n+1}}{\sqrt{n+1}-\sqrt{n}}
$$
-/
theorem number_theory_163284 (n : ℕ) :
    ¬ ∃ m : ℤ, m^2 = ⌊(2 * √(n + 1)) / (√(n + 1) - √n)⌋ := by

  -- We will multiply and divide by the conjugate to remove the denominator:
  have conj : (2 * √(n + 1)) / (√(n + 1) - √n) = 2*n+2 + 2*√n*√(n + 1) := by
    calc (2 * √(n + 1)) / (√(n + 1) - √n)
      _ = (2 * √(n + 1)) / (√(n + 1) - √n) * ((√(n + 1) + √n) / (√(n + 1) + √n)) := by
          field_simp
      _ = (2 * √(n + 1)) * ((√(n + 1) + √n)) / ((√(n + 1) - √n) * (√(n + 1) + √n)) :=
          div_mul_div_comm (2 * √(n + 1)) (√(n + 1) - √n) (√(n + 1) + √n) (√(n + 1) + √n)
      _ = (2 * √(n + 1)) * ((√(n + 1) + √n)) / 1 := by
          have : (√(n + 1) - √n) * (√(n + 1) + √n) = 1 := by
            have : (√(n + 1) - √n) * (√(n + 1) + √n) = √(n + 1)^2 - √n^2 := by linarith
            have : √(n + 1)^2 - √n^2 = n+1 - n := by field_simp
            linarith
          rw [this]
      _ = (2 * √(n + 1)) * ((√(n + 1) + √n))              := by simp
      _ = (2 * √(n + 1)) * √(n + 1) + (2 * √(n + 1)) * √n := by rw [mul_add]
      _ = 2 * (√(n + 1) * √(n + 1)) + (2 * √(n + 1)) * √n := by rw [mul_assoc]
      _ = 2 * (n + 1) + (2 * √(n + 1)) * √n := by rw [Real.mul_self_sqrt]; linarith
      _ = 2 * n + 2 + 2 * √n * √(n + 1)     := by linarith

  -- Now it becomes possible to calculate the floor of the expression, via the rewrite:
  have conj_floor : ⌊2*n+2 + 2*√n*√(n + 1)⌋ = 4*n+2 := by
    have : ⌊(2*n+2) + 2*√n*√(n + 1)⌋ = (2*n+2) + ⌊2*√n*√(n + 1)⌋ := by
      rw [← Int.floor_int_add]; norm_cast

    -- To calculate the floor, we need to prove two inequalities that bound the expression
    have : ⌊2*√n*√(n + 1)⌋ = 2*n := by
      have : 2*n ≤ 2*√n*√(n + 1) := by
        have : n ≤ √n*√(n + 1) := by
          have neq : n = √n*√n := by simp_all only [Nat.cast_nonneg, Real.mul_self_sqrt]
          nth_rw 1 [neq]
          apply mul_le_mul
          . linarith
          . gcongr; linarith
          . exact Real.sqrt_nonneg n
          . exact Real.sqrt_nonneg n
        linarith
      -- The idea here is that $n(n+1) = n^2+n < n^2+n+1/4 = (n+1/2)^2$
      have : 2*√n*√(n+1) < 2*n+1 := by
        have help : √(n*(n+1)) < √((n+1/2)^2) := by
          apply Real.sqrt_lt_sqrt
          . apply mul_nonneg <;> linarith
          . linarith

        calc 2*√n*√(n+1)
          _ = 2*√(n*(n+1))   := by rw [Real.sqrt_mul] <;> linarith
          _ < 2*√((n+1/2)^2) := by
              apply (mul_lt_mul_iff_of_pos_left _).mpr
              . exact help
              . linarith
          _ = 2*(n+1/2 : ℝ)  := by rw [Real.sqrt_sq]; linarith
          _ = (2*n+1 : ℝ)    := by linarith

      apply Int.floor_eq_iff.mpr
      constructor <;>
      simp_all only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    linarith
  have : ⌊(2 * √(n + 1)) / (√(n + 1) - √n)⌋ = 4*n+2 := by rw [conj, conj_floor]

  -- The idea is to show that a perfect square cannot be 2 modulo 4, a contradiction.
  intro h             -- Argue by contradiction
  obtain ⟨m, hm⟩ := h -- Assume there is an $m$
  have : m^2 = 4*n+2 := by linarith
  have msq_mod_4 : m^2 ≡ 2 [ZMOD 4] := by
    rw [this]
    nth_rw 2 [← zero_add 2]
    apply Int.ModEq.add_right
    apply Int.modEq_zero_iff_dvd.mpr
    omega

  -- Now we consider cases: $m$ is even or odd
  rcases m.even_or_odd with meven | modd
  . obtain ⟨k, hk⟩ := meven
    subst m
    have twok : (k+k)^2 = 4*k^2 := by linarith
    -- Show $4k^2$ is both 0 and 2 modulo 4, which is a contradiction:
    have : 4*k^2 ≡ 0 [ZMOD 4] := by apply Int.modEq_zero_iff_dvd.mpr; omega
    rw [twok] at msq_mod_4
    omega
  . obtain ⟨k, hk⟩ := modd
    subst m
    have twok1 : (2*k+1)^2 = 4*(k^2 + k) + 1 := by linarith
    -- Show $4(k^2 + k) + 1$ is both 0 and 1 modulo 4, which is a contradiction:
    have : 4*(k^2 + k)+1 ≡ 0 [ZMOD 4] := by apply Int.modEq_zero_iff_dvd.mpr; omega
    rw [twok1] at msq_mod_4
    omega
