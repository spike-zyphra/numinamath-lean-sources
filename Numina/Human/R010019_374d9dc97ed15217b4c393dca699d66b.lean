import Mathlib

/- The equation $2000x^6 + 100x^5 + 10x^3 + x - 2 = 0$ has exactly two real roots,
one of which is $\frac{m + \sqrt{n}}{r}$, where $m$, $n$ and $r$ are integers,
$m$ and $r$ are relatively prime, and $r > 0$. Find $m + n + r$. -/
theorem algebra_97378 (f : ℝ → ℝ) (hf : f = fun x => 2000 * x ^ 6 + 100 * x ^ 5 + 10 * x ^ 3 + x - 2)
    (x : ℝ) (hx : f x = 0) (m n r : ℤ) (hm : m.gcd r = 1) (hn : n ≥ 0) (hr : r > 0) (hroot : x = (m + √n) / r) :
    m + n + r = 200 := by

  -- We can factor the polynomial pulling out $1000x^6 - 1$ and noting that
  -- is it a difference of cubes
  have r1 : f x = (20 * x ^ 2 + x - 2) * (100 * x ^ 4 + 10 * x ^ 2 + 1) := by
    calc
      f x = 2000 * x ^ 6 + 100 * x ^ 5 + 10 * x ^ 3 + x - 2 := by rw [hf]
      _ = 2 * (1000 * x ^ 6 - 1) + x * (100 * x ^ 4 + 10 * x ^ 2 + 1) := by ring
      _ = 2 * (10 * x ^ 2 - 1) * (100 * x ^ 4 + 10 * x ^ 2 + 1) + x * (100 * x ^ 4 + 10 * x ^ 2 + 1) := by ring
      _ = (20 * x ^ 2 + x - 2) * (100 * x ^ 4 + 10 * x ^ 2 + 1) := by ring

  -- The second factor is always positive so the first factor must be 0
  have r2 : 20 * x ^ 2 + x - 2 = 0 := by
    cases mul_eq_zero.mp (by rw [← r1, hx])
    . assumption
    . exfalso; nlinarith

  -- We can use the quadratic formula to find the roots
  have r3 : x = (-1 + √161) / 40 ∨ x = (-1 - √161) / 40 := by
    have hd : discrim 20 1 (-2) = √161 * √161 := by norm_num [discrim]
    have hp : 20 * (x * x) + 1 * x + (-2) = 0 := by norm_num [← pow_two x]; exact r2
    rw [quadratic_eq_zero_iff (by norm_num) hd x] at hp
    norm_num at hp
    exact hp

  -- Now we must match up the roots with the form from the question. First we show
  -- that 161 is squarefree and thus $\sqrt{161}$ is irrational.
  have squarefree_161 : Squarefree 161 := (Nat.squarefree_mul (by norm_num)).mpr
    ⟨Irreducible.squarefree (show Nat.Prime 7 by norm_num), Irreducible.squarefree (show Nat.Prime 23 by norm_num)⟩

  have not_square_161 : ¬IsSquare 161 := by
    rintro ⟨n, hn⟩
    have : n = 1 := Nat.isUnit_iff.mp (squarefree_161 n (by rw [hn]))
    rw [this] at hn
    contradiction

  have irrational_sqrt_161 : Irrational √161 := irrational_sqrt_natCast_iff.mpr not_square_161

  -- Now we can match up coefficients in rational equations involving $\sqrt{161}$.
  have sqrt_161_match (a b c d : ℚ) (hb : b ≠ 0) (hd : d ≠ 0) (h : a + b * √161 = c + d * √n) : ∃ k : ℕ, a = c ∧ b = d * k ∧ n = 161 * k ^ 2 := by
    -- First move radicals to one side
    have eq1 : b * √161 - d * √n = c - a := by linarith
    -- Square both sides and simplify
    have : (b * √161 - d * √n) ^ 2 = (c - a) ^ 2 := by rw [eq1]
    have : -(2 * b * d) * √161 * √n = (c - a) ^ 2 - b ^ 2 * √161 ^ 2 - d ^ 2 * √n ^ 2 := by linarith
    have : √(161 * n) = ((c - a) ^ 2 - b ^ 2 * 161 - d ^ 2 * n) / -(2 * b * d) := by field_simp; simp [hn, hb, hd] at this; linarith
    -- Thus $\sqrt{161n}$ is rational
    have : ¬Irrational √↑(161 * n) := by
      push_cast
      rw [this]
      norm_cast
      exact Rat.not_irrational _
    -- Thus, $161n$ is a square of some integer k'
    have : IsSquare (161 * n) := by
      rw [irrational_sqrt_intCast_iff_of_nonneg (show 0 ≤ 161 * n by simp [hn]), not_not] at this
      exact this
    obtain ⟨k', hk'⟩ : ∃ k' : ℤ, 161 * n = k' ^ 2 := (isSquare_iff_exists_sq _).mp this
    -- WLOG we can assume $k'$ is a natural number
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, 161 * n = k' ^ 2 := ⟨Int.natAbs k', by simp [hk']⟩
    -- This implies $n = 161 k^2$ for some integer $k$
    have : 161 ∣ k' ^ 2 := by zify; omega
    have : 161 ∣ k' := (Squarefree.dvd_pow_iff_dvd squarefree_161 (by norm_num)).mp this
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k' = 161 * k := this
    have eq_n : n = 161 * k ^ 2 := by
      refine mul_left_cancel₀ (show 161 ≠ 0 by norm_num) ?_
      rw [hk', hk]
      norm_cast
      ring_nf
    -- We can substitute this back into eq1 to get equations for $a$ and $b$
    have eq2 : (b - d * k) * √161 = c - a := by
      rw [eq_n] at eq1
      simp at eq1
      linarith
    have : b - d * k = 0 := by_contradiction fun h => by
      have := Irrational.rat_mul irrational_sqrt_161 h
      push_cast at this
      rw [eq2] at this
      norm_cast at this
      have := Rat.not_irrational (c - a)
      contradiction
    have eq_b_d : b = d * k := by linarith
    have eq_a_c : a = c := by
      norm_cast at eq2
      rw [eq_b_d] at eq2
      simp at eq2
      norm_cast at eq2
      linarith
    exact ⟨k, eq_a_c, eq_b_d, eq_n⟩

  -- Thus we have values for m, n, and r for the first root, and a contradiction for the second root
  have r4 : m = -1 ∧ n = 161 ∧ r = 40 := by
    have : r ≠ 0 := by linarith
    cases r3 with
    | inl h =>
      have : (-1 / 40 : ℚ) + (1 / 40 : ℚ) * √161 = (m / r : ℚ) + (1 / r : ℚ) * √n := by
        push_cast
        field_simp
        rw [hroot] at h
        field_simp at h
        exact symm h
      obtain ⟨k, h1, h2, h3⟩ := sqrt_161_match (-1 / 40) (1 / 40) (m / r) (1 / r) (by norm_num) (by simpa) this
      obtain ⟨eq_m, eq_r⟩ := Rat.div_int_inj (by norm_num) hr (by norm_num) hm h1
      norm_cast at eq_m eq_r
      rw [← eq_r] at h2
      simp at h2
      rw [h2] at h3
      simp at h3
      norm_cast at h3
      exact ⟨symm eq_m, h3, symm eq_r⟩
    | inr h =>
      have : (-1 / 40 : ℚ) + (-1 / 40 : ℚ) * √161 = (m / r : ℚ) + (1 / r : ℚ) * √n := by
        push_cast
        field_simp
        rw [hroot] at h
        field_simp at h
        exact symm h
      obtain ⟨k, h1, h2, h3⟩ := sqrt_161_match (-1 / 40) (-1 / 40) (m / r) (1 / r) (by norm_num) (by simpa) this
      obtain ⟨eq_m, eq_r⟩ := Rat.div_int_inj (by norm_num) hr (by norm_num) hm h1
      norm_cast at eq_m eq_r
      rw [← eq_r] at h2
      field_simp at h2
      linarith

  -- And finally, we can sum the values
  simp [r4]