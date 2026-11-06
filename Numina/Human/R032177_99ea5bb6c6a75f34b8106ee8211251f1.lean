import Mathlib

/-Let the first term of a geometric sequence be $\frac{3}{4}$, and let the second term be $15$. What is the smallest $n$ for which the $n$th term of the sequence is divisible by one million?-/
theorem algebra_12265 {a : ℕ → ℝ} (ha : a 0 = 3 / 4) (ha1 : a 1 = 15)
    (hge : ∃ r, ∀ n, a n = a 0 * r ^ n) :
    IsLeast {n | 1 ≤ n ∧ ∃ (k : ℤ), 1000000 * k = a n } 6 := by
      obtain ⟨r, hr⟩ := hge
      have hr' := hr
      -- The common ratio is $$\frac{15}{\frac{3}{4}} = 20$$Therefore,
      -- the $n$th term is $(20^{n-1}) \left(\frac{3}{4}\right)$.
      specialize hr' 1
      simp [ha, ha1] at hr'
      have r20 : r = 20 := by linarith
      simp [r20, ha] at hr
      constructor
      · -- Verify that 6 satisfy the condition.
        simp
        specialize hr 6
        ring_nf at hr
        simp [hr]
        use 48
        simp
        linarith
      · -- If one million (aka $10^6$) divides the $n$th term, then it must be divisible by $5^6$.
        -- This can only happen if $n$ is at least $6$, or $n \ge 6$.
        intro m hm
        simp at hm
        specialize hr m
        rw [show (20 : ℝ) = 4 * 5 by linarith] at hr
        rw [hr, mul_pow, show (1000000 : ℝ) = 2^6 * 5^ 6 by linarith] at hm
        obtain ⟨k, hk⟩ := hm.2
        field_simp at hk
        norm_cast at hk
        simp [mul_assoc] at hk
        have : (1000000 : ℤ) ∣ 3 * (4 ^ m * 5 ^ m) := Dvd.intro (k * 4) hk
        rw [show (1000000 : ℤ) = 2^6 * 5^ 6 by linarith] at this
        have := dvd_of_mul_left_dvd this
        norm_cast at this
        have := (Nat.Coprime.dvd_mul_left (by exact rfl) ).1 this
        have := (Nat.Coprime.dvd_mul_left (by exact Nat.Coprime.pow 6 m rfl) ).1 this
        exact Nat.pow_dvd_pow_iff_le_right'.mp this
