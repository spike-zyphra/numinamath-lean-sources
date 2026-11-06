import Mathlib
set_option maxHeartbeats 500000

/-!
Let a, b, c be positive integers, distinct from each other.Let p = a*b + b*c + c*a, and assume p is a prime number.Without loss of generality, assume a < b < c.
Prove：1. a^2, b^2, c^2 are distinct in ZMod p.2. a^3, b^3, c^3 are distinct in ZMod p.
-/
/-- WLOG Assume a < b < c and p = a*b + b*c + c*a is prime -/
theorem distinct_squares_and_cubes_mod_prime {a b c : ℕ}
  (hpos : 0 < a) (hab : a < b) (hbc : b < c)
  (pp : Prime (a*b + b*c + c*a)) :
  -- Distinct squares and cubes in ZMod p
  (a^2 % (a*b + b*c + c*a) ≠ b^2 % (a*b + b*c + c*a) ∧ b^2 % (a*b + b*c + c*a) ≠ c^2 % (a*b + b*c + c*a) ∧ c^2 % (a*b + b*c + c*a) ≠ a^2 % (a*b + b*c + c*a))
  ∧
  (a^3 % (a*b + b*c + c*a) ≠ b^3 % (a*b + b*c + c*a) ∧ b^3 % (a*b + b*c + c*a) ≠ c^3 % (a*b + b*c + c*a) ∧ a^3 % (a*b + b*c + c*a) ≠ c^3 % (a*b + b*c + c*a)) := by
  -- Collect some facts for convenience
  let p := a*b + b*c + c*a
  have hpos : 0 < p := by
    have hb_pos : 0 < b := Nat.lt_trans hpos hab
    have hc_pos : 0 < c := Nat.lt_trans hb_pos hbc
    exact add_pos_of_pos_of_nonneg (add_pos (mul_pos hpos hb_pos) (mul_pos hb_pos hc_pos)) (Nat.zero_le _)

  have p_ne_zero : (p : ℕ) ≠ 0 := Nat.ne_of_gt hpos

  have c_pos : 1 < c := by linarith [hbc]

  have b_gt_a : 0 < b - a := by simp [hab]

  have c_gt_b : 0 < c - b := by simp [hbc]
  have c_gt_a : 0 < c - a := by simp [Nat.lt_trans hab hbc]

  have a_plus_b_lt_p : b + a < p := by calc
        _ < c * b + c * a + a * b := by nlinarith
        _ = p := by ring

  have c_plus_b_lt_p : c + b < p := by calc
        _ < c * b + c * a + a * b := by nlinarith
        _ = p := by ring

  have c_plus_a_lt_p : c + a < p := by calc
        _ < c * b + c * a + a * b := by nlinarith
        _ = p := by ring

  have b_ge_a : b^3 ≥ a^3 := Nat.pow_le_pow_left (by linarith) 3
  have c_ge_b : c^3 ≥ b^3 := Nat.pow_le_pow_left (by linarith) 3
  have c_ge_a : c^3 ≥ a^3 := Nat.pow_le_pow_left (by linarith) 3


  -- Auxiliary lemma
  have mod_eq_iff_dvd (x y d : ℕ) (h : x % d = y % d) (hle: y ≤ x):  d ∣ x - y := by exact (Nat.modEq_iff_dvd' hle).mp (id (Eq.symm h))


  -- ---- 1) Distinct squares ----
  -- a^2 ≠ b^2 mod p
  have sq_ab : a^2 % p ≠ b^2 % p := by
    by_contra H
    -- Get p ∣ (b^2 - a^2) from the modular equality
    have dvd1 : p ∣ (b^2 - a^2) := by
      have h1 : b^2 % p = a^2 % p := H.symm
      exact mod_eq_iff_dvd (b^2) (a^2) p h1 (by nlinarith)
    -- Use the factorization b^2 - a^2 = (b - a) * (b + a)
    have factor : b^2 - a^2 = (b + a) * (b - a) := by
      rw [Nat.sq_sub_sq]

    rw [factor] at dvd1
    -- Apply the prime divisibility property
    rcases pp.dvd_mul.1 dvd1 with h1 | h2
    · -- Case: p ∣ (b + a)
      have pos : p < p := by calc
        p ≤ b + a := Nat.le_of_dvd (by nlinarith) h1
        _ < p := a_plus_b_lt_p

      exact Nat.lt_irrefl p pos

    · -- Case: p ∣ (b - a)
      have pos₂ : p < p := by calc
        p ≤ b - a := Nat.le_of_dvd b_gt_a h2
        _ ≤ b + a := by omega
        _ < p := a_plus_b_lt_p
      exact Nat.lt_irrefl p pos₂

  -- b^2 ≠ c^2 mod p
  have sq_bc : b^2 % p ≠ c^2 % p := by
    by_contra H
    have dvd1 : p ∣ (c^2 - b^2) := by
      have h1 : c^2 % p = b^2 % p := H.symm
      exact mod_eq_iff_dvd (c^2) (b^2) p h1 (by nlinarith)
    have factor : c^2 - b^2 = (c + b) * (c - b) := by
      rw [Nat.sq_sub_sq]

    rw [factor] at dvd1
    rcases pp.dvd_mul.1 dvd1 with h1 | h2
    · have pos : p < p := by calc
        p ≤ c + b := Nat.le_of_dvd (by linarith) h1
        _ < p := c_plus_b_lt_p
      exact Nat.lt_irrefl p pos
    · have c_gt_b : 0 < c - b := by simp [hbc]
      have pos₂ : p < p := by calc
        p ≤ c - b := Nat.le_of_dvd c_gt_b h2
        _ ≤ c + b := by omega
        _ < p := c_plus_b_lt_p
      exact Nat.lt_irrefl p pos₂

  -- c^2 ≠ a^2 mod p
  have sq_ca : c^2 % p ≠ a^2 % p := by
    by_contra H
    have dvd1 : p ∣ (c^2 - a^2) := by
      have h1 : c^2 % p = a^2 % p := H
      exact mod_eq_iff_dvd (c^2) (a^2) p h1 (by nlinarith)
    have factor : c^2 - a^2 = (c + a) * (c - a) := by
      rw [Nat.sq_sub_sq]

    rw [factor] at dvd1
    rcases pp.dvd_mul.1 dvd1 with h1 | h2
    · have pos : p < p := by calc
        p ≤ c + a := Nat.le_of_dvd (by linarith) h1
        _ < p := c_plus_a_lt_p
      exact Nat.lt_irrefl p pos
    · have c_gt_a : 0 < c - a := by simp [Nat.lt_trans hab hbc]
      have pos₂ : p < p := by calc
        p ≤ c - a := Nat.le_of_dvd c_gt_a h2
        _ ≤ c + a := by omega
        _ < p := c_plus_a_lt_p
      exact Nat.lt_irrefl p pos₂

  -- ---- 2) Distinct cubes ----
  have cu_ab : a^3 % p ≠ b^3 % p := by
    by_contra Hc
    have dvd2 : p ∣ (b^3 - a^3) := mod_eq_iff_dvd _ _ p Hc.symm (by linarith)

    have factor_cube : (b - a) * (a^2 + a * b + b^2) = b^3 - a^3 := by calc
      _ = b * (a^2 + a * b + b^2) - a * (a^2 + a * b + b^2) := Nat.sub_mul b a (a ^ 2 + a * b + b ^ 2)
      _ = (b * a^2 + a * b^2 + b^3) - (a^3 + a^2 * b + a * b^2) := by ring_nf

      _ = (b^3 + (a^2 * b + a * b^2)) - (a^3 + (a^2 * b + a * b^2)) := by ring_nf
      _ = b^3 - a^3 := Nat.add_sub_add_right (b ^ 3) (a ^ 2 * b + a * b ^ 2) (a ^ 3)

    rw [factor_cube.symm] at dvd2
    rcases pp.dvd_mul.1 dvd2 with h1 | h2
    · -- Modulo squares equal to modulo cubes leads to a contradiction
      have pos₂ : p < p := by calc
        p ≤ b - a := Nat.le_of_dvd b_gt_a h1
        _ ≤ b + a := by omega
        _ < p := a_plus_b_lt_p
      exact Nat.lt_irrefl p pos₂

    · -- p ∣ (a^2 + a*b + b^2)
      -- Add p = a*b + b*c + c*a to get p ∣ (a+b)(a+b+c)
      have dvd_prod : p ∣ (a + b)*(a + b + c) := by
        have : a^2 + a*b + b^2 + (a*b + b*c + c*a) = (a+b)*(a+b+c) := by ring
        -- p | (a^2 + a*b + b^2) and  p | (a*b + b*c + c*a) ⇒ p | (a+b)(a+b+c)
        rw [← this]
        exact dvd_add h2 (dvd_refl p)

      rcases pp.dvd_mul.1 dvd_prod with h3 | h4
      · -- p ∣ a + b, but this leads to a contradiction
        have pos : p < p := by calc
          p ≤ a + b := Nat.le_of_dvd (by linarith) h3
          _ < p := by rw [add_comm]; exact a_plus_b_lt_p
        exact Nat.lt_irrefl p pos
      · -- p ∣ a + b + c, but this leads to a contradiction
        have pos : p < p := by calc
          p ≤ a + b + c := Nat.le_of_dvd (by linarith) h4
          _ < a*b + b*c + c*a := by nlinarith
          _ = p := by ring
        exact Nat.lt_irrefl p pos

  have cu_bc : b^3 % p ≠ c^3 % p := by
    by_contra Hc
    have dvd2 : p ∣ (c^3 - b^3) := mod_eq_iff_dvd _ _ p Hc.symm (by linarith)
    have factor_cube : (c - b) * (b^2 + b * c + c^2) = c^3 - b^3 := by calc
      _ = c * (b^2 + b * c + c^2) - b * (b^2 + b * c + c^2) := Nat.sub_mul c b (b ^ 2 + b * c + c ^ 2)
      _ = (c * b^2 + b * c^2 + c^3) - (b^3 + b^2 * c + b * c^2) := by ring_nf
      _ = (c^3 + (b^2 * c + b * c^2)) - (b^3 + (b^2 * c + b * c^2)) := by ring_nf
      _ = c^3 - b^3 := Nat.add_sub_add_right (c ^ 3) (b ^ 2 * c + b * c ^ 2) (b ^ 3)
    rw [factor_cube.symm] at dvd2
    rcases pp.dvd_mul.1 dvd2 with h1 | h2
    · -- Modulo squares equal to modulo cubes leads to a contradiction
      have pos₂ : p < p := by calc
        p ≤ c - b := Nat.le_of_dvd c_gt_b h1
        _ ≤ c + b := by omega
        _ < p := c_plus_b_lt_p
      exact Nat.lt_irrefl p pos₂

    · -- p ∣ (b^2 + b*c + c^2)
      have dvd_prod : p ∣ (b + c)*(b + c + a) := by
        have : b^2 + b*c + c^2 + (a*b + b*c + c*a) = (b+c)*(b+c+a) := by ring
        rw [← this]
        exact dvd_add h2 (dvd_refl p)
      rcases pp.dvd_mul.1 dvd_prod with h3 | h4
      · -- p ∣ b + c, but this leads to a contradiction
        have pos : p < p := by calc
          p ≤ b + c := Nat.le_of_dvd (by linarith) h3
          _ < p := by rw [add_comm]; exact c_plus_b_lt_p
        exact Nat.lt_irrefl p pos
      · -- p ∣ b + c + a, but this leads to a contradiction
        have pos : p < p := by calc
          p ≤ b + c + a := Nat.le_of_dvd (by linarith) h4
          _ < a*b + b*c + c*a := by nlinarith
          _ = p := by ring
        exact Nat.lt_irrefl p pos

  have cu_ac : a^3 % p ≠ c^3 % p := by
    by_contra Hc
    have dvd2 : p ∣ (c^3 - a^3) := mod_eq_iff_dvd _ _ p Hc.symm (by linarith)
    have factor_cube : (c - a) * (a^2 + a * c + c^2) = c^3 - a^3 := by calc
      _ = c * (a^2 + a * c + c^2) - a * (a^2 + a * c + c^2) := Nat.sub_mul c a (a ^ 2 + a * c + c ^ 2)
      _ = (c * a^2 + a * c^2 + c^3) - (a^3 + a^2 * c + a * c^2) := by ring_nf
      _ = (c^3 + (a^2 * c + a * c^2)) - (a^3 + (a^2 * c + a * c^2)) := by ring_nf
      _ = c^3 - a^3 := Nat.add_sub_add_right (c ^ 3) (a ^ 2 * c + a * c ^ 2) (a ^ 3)
    rw [factor_cube.symm] at dvd2
    rcases pp.dvd_mul.1 dvd2 with h1 | h2
    · -- Modulo squares equal to modulo cubes leads to a contradiction
      have pos₂ : p < p := by calc
        p ≤ c - a := Nat.le_of_dvd c_gt_a h1
        _ ≤ c + a := by omega
        _ < p := c_plus_a_lt_p
      exact Nat.lt_irrefl p pos₂
    · -- p ∣ (a^2 + a*c + c^2)
      have dvd_prod : p ∣ (a + c)*(a + c + b) := by
        have : a^2 + a*c + c^2 + (a*b + b*c + c*a) = (a+c)*(a+c+b) := by ring
        rw [← this]
        exact dvd_add h2 (dvd_refl p)
      rcases pp.dvd_mul.1 dvd_prod with h3 | h4
      · -- p ∣ a + c, but this leads to a contradiction
        have pos : p < p := by calc
          p ≤ a + c := Nat.le_of_dvd (by linarith) h3
          _ < p := by rw [add_comm]; exact c_plus_a_lt_p
        exact Nat.lt_irrefl p pos
      · -- p ∣ a + c + b, but this leads to a contradiction
        have pos : p < p := by calc
          p ≤ a + c + b := Nat.le_of_dvd (by linarith) h4
          _ < a*b + b*c + c*a := by nlinarith
          _ = p := by ring
        exact Nat.lt_irrefl p pos

  exact And.intro ⟨sq_ab, sq_bc, sq_ca⟩ ⟨cu_ab, cu_bc, cu_ac⟩