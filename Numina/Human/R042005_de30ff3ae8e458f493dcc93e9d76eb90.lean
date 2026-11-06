import Mathlib

/- 4. Let $a, b$, and $c$ be natural numbers.

a) If $ab$ and $bc$ are cubes of natural numbers, prove that $a^{2} c$ is also a cube of a natural number.

b) If $a^{4} b, b^{8} c^{5}$, and $c^{7} a$ are cubes of natural numbers, prove that $a, b$, and $c$ are cubes of natural numbers. -/
theorem number_theory_104979 (a b c : ℕ) :
    ( (b ≠ 0) → (∃ m n, a * b = m^3 ∧ b * c = n^3) → ∃ p, a^2 * c = p^3 ) ∧
    ( (a ≠ 0) → (b ≠ 0) → (c ≠ 0) → (∃ q r s, a^4 * b = q^3 ∧ b^8 * c^5 = r^3 ∧ c^7 * a = s^3) →
      ∃ t u v, a = t^3 ∧ b = u^3 ∧ c = v^3 ) := by
  -- We repeatedly use the lemma that if x and y are natural numbers such that
  -- x and xy are cubes, then y is also a cube (here natural number excludes 0)
  -- The lemma is false if x = 0, (e.g. 0 * 2 = 0, but 2 is not a cube), so this
  -- hypothesis is necessary
  have cube_product: ∀ x y : ℕ, (x ≠ 0) → (∃ q, x^3 * y = q^3) → ∃ r, y = r^3 := by
    intro x y x_nz ⟨q, hq⟩
    have x_cubed_nz: x^3 ≠ 0 := (pow_ne_zero_iff (by decide)).mpr x_nz
    have x_cubed_div_q_cubed: x^3 ∣ q^3 := dvd_of_mul_right_eq y hq
    -- The result is still true if q = 0, so we don't require a hypothesis that
    -- q ≠ 0, because otherwise we would have to provide a proof of this every
    -- time we use the lemma
    by_cases q_zero: q = 0
    use 0; rw [zero_pow (by decide)]
    rw [q_zero] at hq
    cases Nat.mul_eq_zero.mp hq
    contradiction
    assumption
    -- We consider the prime factorizations of x and q
    have h_fact: (x^3).factorization ≤ (q^3).factorization := by
      apply (Nat.factorization_le_iff_dvd x_cubed_nz _).mpr x_cubed_div_q_cubed
      exact (pow_ne_zero_iff (by decide)).mpr q_zero
    have h_x_div_q: x ∣ q := by
      apply (Nat.factorization_le_iff_dvd x_nz q_zero).mp
      repeat rw [Nat.factorization_pow] at h_fact
      intro s
      -- Three times the exponent of each prime in x is at most three times
      -- the exponent of the same prime in q
      have: 3 * x.factorization s ≤ 3 * q.factorization s := h_fact s
      linarith
    let ⟨r, hr⟩ := h_x_div_q
    rw [hr, mul_pow] at hq
    use r
    exact (Nat.mul_right_inj x_cubed_nz).mp hq

  -- Prove each subresult separately
  constructor

  intro b_nz ⟨m, n, ⟨hm, hn⟩⟩
  -- a^2 b^3 c = (ab)^2 * bc is a product of cubes, hence is a cube
  have: b^3 * (a^2 * c) = (m^2 * n)^3 := calc
    b^3 * (a^2 * c) = (a * b)^2 * (b * c) := by ring
    _ = (m^2 * n)^3 := by rw [hm, hn]; ring
  -- Thus by the lemma, a^2 c is a cube
  apply cube_product b (a^2 * c) b_nz; use m^2 * n

  intro a_nz b_nz c_nz ⟨q, r, s, ⟨hq, ⟨hr, hs⟩⟩⟩
  have ab_cube: ∃ t, a*b = t^3 := by
    -- By assumption, a^3 (ab) = a^4 b is a cube
    have: a^3 * (a*b) = q^3 := by rw [← hq]; ring
    -- So by the lemma, ab is a cube
    apply cube_product a (a*b) a_nz; use q
  let ⟨t, ht⟩ := ab_cube

  have bsq_csq_cube: ∃ u, b^2 * c^2 = u^3 := by
    -- By assumption, b^8 c^5 is a cube
    have: (b^2 * c)^3 * (b^2 * c^2) = r^3 := by rw [← hr]; ring
    -- Since b^6 c^3 is a cube, the lemma implies b^2 c^2 is a cube
    apply cube_product (b^2 * c) (b^2 * c^2)
    simp [b_nz, c_nz]
    use r
  let ⟨u, hu⟩ := bsq_csq_cube

  have ca_cube: ∃ v, c*a = v^3 := by
    -- By assumption, c^7 a is a cube
    have: (c^2)^3 * (c*a) = s^3 := by rw [← hs]; ring
    -- So since c^6 is a cube, we get that ca is a cube
    apply cube_product (c^2) (c*a)
    simp [a_nz, c_nz]
    use s
  let ⟨v, hv⟩ := ca_cube

  have a_csq_cube: ∃ w, a * c^2 = w^3 := by
    -- Now ab^3 c^2 = (ab) * (b^2 c^2) is a product of cubes, hence a cube
    have: b^3 * (a * c^2) = (t * u)^3 := by rw [mul_pow, ← ht, ← hu]; ring
    -- So by the lemma, ac^2 is a cube
    apply cube_product b (a * c^2) b_nz; use t * u
  let ⟨w, hw⟩ := a_csq_cube

  have c_cube: ∃ x, c = x^3 := by
    have: v^3 * c = w^3 := by rw [←hv, ←hw]; ring
    -- We now use the lemma by noting that ac and ac * c are both cubes
    apply cube_product v c
    by_contra v_zero
    rw [v_zero, zero_pow (by decide)] at hv
    simp [a_nz, c_nz] at hv
    use w
  let ⟨x, hx⟩ := c_cube

  have a_cube: ∃ y, a = y^3 := by
    have: x^3 * a = v^3 := by rw [← hx, ←hv]
    -- Since ac is a cube, and c is a cube, a is a cube
    apply cube_product x a
    by_contra x_zero
    rw [x_zero, zero_pow (by decide)] at hx
    contradiction
    use v
  let ⟨y, hy⟩ := a_cube

  have b_cube: ∃ z, b = z^3 := by
    have: y^3 * b = t^3 := by rw [← hy, ← ht]
    -- And finally, since ab is a cube, and a is a cube, we get that b is a cube
    apply cube_product y b
    by_contra y_zero
    rw [y_zero, zero_pow (by decide)] at hy
    contradiction
    use t
  let ⟨z, hz⟩ := b_cube

  use y, z, x