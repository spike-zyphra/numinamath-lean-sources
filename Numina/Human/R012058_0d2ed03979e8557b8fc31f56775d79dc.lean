import Mathlib
open Real Finset Nat
set_option linter.unusedVariables false
noncomputable section

-- Lemma 1: $z(z + 3)$ mod $4$ is $0$ or $1$ implies $z$ mod $4$ is $0$ or $1$.
lemma z_mod_4 (z : ℕ) : z * (z + 3) % 4 = 0 ∨ z * (z + 3) % 4 = 1 → z % 4 = 0 ∨ z % 4 = 1 := by
  intro h
  have h_mod : z % 4 < 4 := Nat.mod_lt z (by norm_num)
  have h_cases : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
  rcases h_cases with hz0 | hz1 | hz2 | hz3
  · left; exact hz0
  · right; exact hz1
  · exfalso
    have h_z3 : (z + 3) % 4 = (z % 4 + 3) % 4 := Nat.add_mod z 3 4
    rw [hz2] at h_z3
    have : (z + 3) % 4 = 1 := by norm_num [h_z3]
    have h_prod : z * (z + 3) % 4 = (z % 4 * ((z + 3) % 4)) % 4 := Nat.mul_mod _ _ 4
    rw [hz2, this] at h_prod
    simp [norm_num] at h_prod
    cases h with
    | inl h0 => linarith
    | inr h1 => linarith
  · exfalso
    have h_z3 : (z + 3) % 4 = (z % 4 + 3) % 4 := Nat.add_mod z 3 4
    rw [hz3] at h_z3
    have : (z + 3) % 4 = 2 := by norm_num [h_z3]
    have h_prod : z * (z + 3) % 4 = (z % 4 * ((z + 3) % 4)) % 4 := Nat.mul_mod _ _ 4
    rw [hz3, this] at h_prod
    simp [norm_num] at h_prod
    cases h with
    | inl h0 => linarith
    | inr h1 => linarith

-- Lemma 2: Square mod $4$ is $0$ or $1$.
lemma square_mod_4 (y : ℕ) : y ^ 2 % 4 = 0 ∨ y ^ 2 % 4 = 1 := by
  cases Nat.mod_two_eq_zero_or_one y with
  | inl h_even =>
    have h_y_even : 2 ∣ y := Nat.dvd_of_mod_eq_zero h_even
    obtain ⟨k, rfl⟩ := h_y_even
    left
    rw [pow_two, Nat.mul_mod]
    simp [Nat.mul_mod]
    norm_num
    have : 2 * k * (2 * k) = 4 * (k * k) := by ring
    rw [this]
    omega
  | inr h_odd =>
    have h_y_odd : y % 2 = 1 := h_odd
    have : Odd y := by exact Nat.odd_iff.mpr h_y_odd
    have : Odd (y : ℤ) := by exact_mod_cast this
    have : (y : ℤ) ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd this
    right
    exact_mod_cast this

/-13.375 Find a three-digit number, knowing that the number of its tens is the geometric mean of the number of hundreds and units. If in its notation the digits of hundreds and units are swapped and the new number is subtracted from the desired one, then the difference will be equal to 297.-/
theorem number_theory_80585 {x y z : ℕ}
    (hx : x ∈ Finset.Ico 1 10) (hy : y ∈ Finset.range 10) (hz : z ∈ Finset.range 10)
    (h_eq : y ^ 2 = x * z) (h_sub : Nat.ofDigits 10 [z, y, x] - Nat.ofDigits 10 [x, y, z] = 297) :
    Nat.ofDigits 10 [z, y, x] = 300 ∨ Nat.ofDigits 10 [z, y, x] = 421 := by
  -- Derive $x = z + 3$ from the difference condition.
  have h_x_z : x = z + 3 := by
    have h_diff : 99 * x - 99 * z = 297 := by
      have h1 : Nat.ofDigits 10 [z, y, x] = z + 10 * y + 100 * x := by simp [Nat.ofDigits];ring
      have h2 : Nat.ofDigits 10 [x, y, z] = x + 10 * y + 100 * z := by simp [Nat.ofDigits];ring
      have : z + 10 * y + 100 * x - (x + 10 * y + 100 * z)  =  99 * x - 99 * z := by omega
      rw [h1, h2,this] at h_sub
      exact h_sub
    have : 297 = 99 * 3 := by norm_num
    rw [this, ← Nat.mul_sub] at h_diff
    have : x - z = 3 := by exact (Nat.mul_right_inj (by norm_num: 99 ≠ 0)).mp h_diff
    omega

  -- Geometric mean condition yields $y^2 = z(z + 3)$.
  have h_y2 : y ^ 2 = z * (z + 3) := by
    rw [h_x_z,mul_comm] at h_eq
    exact h_eq

  -- Useing lemma, derive $z(z + 3)$ mod $4$ eq $0$ or $1$.
  have h_z_mod_4 : z % 4 = 0 ∨ z % 4 = 1 := by
    apply z_mod_4 z
    rw [← h_y2]
    exact square_mod_4 y

  -- Analyze possible values of $z$ and $y$.
  have h_z_y : (z = 0 ∧ y = 0) ∨ (z = 1 ∧ y = 2) := by
    have h_y_9 : y ≤ 9 := by exact Finset.mem_range_succ_iff.mp hy
    have h_z_9 : z ≤ 9 := by nlinarith [hz]
    -- Restrict $z$ to possible values based on mod $4$ constraint.
    cases h_z_mod_4 with
    | inl h_z_0 =>
      have h_z : z = 0 ∨ z = 4 ∨ z = 8 := by omega
      cases h_z with
      | inl h_z_0 =>
        left
        constructor
        · exact h_z_0
        · rw [h_z_0] at h_y2
          nlinarith
      | inr h_z_4_8 =>
        -- Exclude $z = 4, 8$ by showing $y^2 = z(z + 3)$ has no integer solutions.
        cases h_z_4_8 with
        | inl h_z_4 =>
          exfalso
          rw [h_z_4] at h_y2
          simp at h_y2
          have h_lower : 5 < y  := by
            have : 5 ^ 2 < y ^ 2  := by linarith [h_y2]
            exact lt_of_pow_lt_pow_left' 2 this
          have h_upper : y < 6 := by
            have : y ^ 2 < 36 := by linarith [h_y2]
            exact lt_of_pow_lt_pow_left' 2 this
          linarith
        | inr h_z_8 => exfalso; rw [h_z_8] at h_y2; simp at h_y2; nlinarith [h_y_9]
    | inr h_z_1 =>
      -- Exclude $z = 5, 9$ by similar bounds analysis.
      have h_z : z = 1 ∨ z = 5 ∨ z = 9 := by omega
      cases h_z with
      | inl h_z_1 =>
        right
        rw [h_z_1] at h_y2
        simp at h_y2
        constructor
        · exact h_z_1
        · have h_y_eq: Real.sqrt 4 = y := by
            have : (4 : ℝ) = ↑y ^ 2 := by exact_mod_cast h_y2.symm
            exact_mod_cast (Real.sqrt_eq_iff_eq_sq (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ y)).mpr this
          have : Real.sqrt 4 = 2 := by 
            have : (4: ℝ) = 2 ^ 2 := by norm_num
            rw [this]
            linarith [Real.sqrt_sq (by norm_num:(0 : ℝ) ≤ 2)]
          rw [this] at h_y_eq
          exact_mod_cast h_y_eq.symm
      | inr h_z_5_9 =>
        cases h_z_5_9 with
        | inl h_z_5 =>
          exfalso
          rw [h_z_5] at h_y2
          simp at h_y2
          have h_lower : 6 < y  := by
            have : 6 ^ 2 < y ^ 2  := by linarith [h_y2]
            exact lt_of_pow_lt_pow_left' 2 this
          have h_upper : y < 7 := by
            have : y ^ 2 < 49 := by linarith [h_y2]
            exact lt_of_pow_lt_pow_left' 2 this
          linarith
        | inr h_z_9 => exfalso; rw [h_z_9] at h_y2; simp at h_y2; nlinarith [h_y_9]

  -- Verify solutions.
  cases h_z_y with
  | inl h_z0_y0 =>
    left
    have h_digits : Nat.ofDigits 10 [z, y, x] = z + 10 * y + 100 * x := by simp [Nat.ofDigits];ring
    rw [h_digits, h_z0_y0.1, h_z0_y0.2]
    simp [h_x_z,h_z0_y0.1]
  | inr h_z2_y2 =>
    right
    have h_digits : Nat.ofDigits 10 [z, y, x] = z + 10 * y + 100 * x := by simp [Nat.ofDigits];ring
    rw [h_digits, h_z2_y2.1, h_z2_y2.2]
    simp [h_x_z,h_z2_y2.1]
