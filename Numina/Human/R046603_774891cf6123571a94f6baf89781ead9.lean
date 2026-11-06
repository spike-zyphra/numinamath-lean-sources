import Mathlib

/- The number of terms in an arithmetic sequence is $n$, the sum of its terms is $s_{1}$, the sum of the squares of its terms is $s_{2}$, and the sum of the cubes of its terms is $s_{3}$. Show that the following relationship holds:
$$ n^{2} s_{3}-3 n s_{1} s_{2}+2 s_{1}^{2}=0 $$


Determine the terms of the sequence if $s_{1}=8, s_{2}=50, s_{3}=134$. -/
theorem algebra_188294 {a d s₁ s₂ s₃ : ℚ} {n : ℕ} (h₀ : d ≠ 0) (h₁ : ∑ i ∈ Finset.range n, (a + d * i) = s₁)
    (h₂ : ∑ i ∈ Finset.range n, (a + d * i)^2 = s₂) (h₃ : ∑ i ∈ Finset.range n, (a + d * i)^3 = s₃) :
    (n^2 * s₃ - 3 * n * s₁ * s₂ + 2 * s₁^3 = 0) ∧ ((s₁ = 8 ∧ s₂ = 50 ∧ s₃ = 134) → (
      {a + d * i | i ∈ Finset.range n} = {-(5/2), -(3/2), -(1/2), 1/2, 3/2, 5/2, 7/2, 9/2}
    )) := by

  -- First we need to compute the sum, the sum of the squares, and the sum of the cubes of the first n-1 natural numbers. They can all be done by induction.

  have sum_id (n : ℕ) : ∑ i in Finset.range n, i = ((n : ℚ) * (n - 1)) / 2 := by
    induction' n with n ih
    · simp
    · rw [Finset.sum_range_succ, Nat.cast_add, ih]
      simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_succ]
      field_simp
      ring_nf

  have sum_squares (n : ℕ) : ∑ i in Finset.range n, i^2 = ((n : ℚ) * (n - 1) * (2 * n - 1)) / 6 := by
    induction' n with n ih
    · simp
    · rw [Finset.sum_range_succ, Nat.cast_add, ih]
      simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_succ]
      field_simp
      ring_nf

  have sum_cubes (n : ℕ) : ∑ i in Finset.range n, i^3 = (((n : ℚ) * (n - 1)) / 2)^2 := by
    induction' n with n ih
    · simp
    · rw [Finset.sum_range_succ, Nat.cast_add, ih]
      simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_succ]
      field_simp
      ring_nf

  -- To compute the sum, the sum of the squares, and the sum of the cubes of an arithmetic sequence, we can use distributivity to reduce to the case of the first n-1 natural numbers.

  have pol_id : n ^ 2 * s₃ - 3 * n * s₁ * s₂ + 2 * s₁ ^ 3 = (0 : ℚ) := by
    rw [← h₁, ← h₂, ← h₃]
    simp_rw [add_sq, pow_three]
    ring_nf
    repeat rw [Finset.sum_add_distrib]
    simp_rw [mul_pow]
    repeat rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    repeat rw [← Finset.sum_mul]
    repeat rw [← Finset.mul_sum]
    simp_rw [← Nat.cast_pow, ← Nat.cast_sum]
    rw [← Nat.cast_sum, Nat.cast_pow]
    rw [sum_id, sum_squares, sum_cubes]
    field_simp
    ring_nf

  constructor
  · -- The first part of the theorem is just the polynomial identity we have just proved.
    exact pol_id
  · -- In order to solve the second part, we substitute the values of the sums and deduce a quadratic identity for n.
    intro ⟨hs₁, hs₂, hs₃⟩
    rw [hs₁, hs₂, hs₃] at pol_id
    rw [(by ring : (n : ℚ) ^ 2 * 134 - 3 * n * 8 * 50 + 2 * 8 ^ 3 = 2 * (67 * n - 64) * ((n : ℚ) - 8))] at pol_id
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at pol_id
    -- The quadratic has two solutions, n = 64/67 and n = 8.
    rcases pol_id with hn | hn
    · -- The first one is impossible, as n is an integer.
      rcases n with _ | n
      · ring_nf at hn; contradiction
      · rw [Nat.cast_add] at hn; ring_nf at hn; linarith
    · -- We can now get a quadratic system of equations for a and d.
      rw [sub_eq_zero] at hn
      apply Rat.natCast_inj.mp at hn
      rw [hn] at h₁ h₂ h₃
      rw [hs₁] at h₁; rw [hs₂] at h₂; rw [hs₃] at h₃
      repeat rw [Finset.sum_range_succ] at h₁ h₂ h₃
      rw [Finset.sum_range_zero] at h₁ h₂ h₃
      ring_nf at h₁ h₂ h₃
      -- We can compute the value of a in terms of d.
      have : a = 1 - 7 * d / 2 := by
        field_simp
        apply mul_right_cancel₀ (by norm_num : (4 : ℚ) ≠ 0)
        ring_nf
        nth_rw 2 [← h₁]
        ring_nf
      -- Substituting in the second equation, we get d = 1 or d = -1.
      rw [this] at h₂
      have that : d = 1 ∨ d = -1 := by
        ring_nf at h₂
        exact sq_eq_one_iff.mp (by linarith)

      -- Now we can just substitute the values of a, d, n and compute the terms of the sequence.
      ext x
      constructor
      · intro hx
        rw [Set.mem_setOf_eq] at hx
        obtain ⟨i, ⟨hi, hi'⟩⟩ := hx
        rw [Finset.mem_range, hn] at hi
        interval_cases i
        all_goals
          rw [← hi', this]
          rcases that with h | h <;> rw [h]
          all_goals native_decide
      · intro hx
        rw [Set.mem_setOf_eq]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        use ((x - a) * d).floor.toNat
        rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;> rcases that with h | h
        all_goals rw [this, h, hx, hn]
        all_goals  native_decide