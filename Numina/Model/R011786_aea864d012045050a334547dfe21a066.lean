import Mathlib

theorem algebra_320379: {p: ℤ | Prime p ∧ 0 < p ∧
    ∃ x y: ℤ, x ^ 2 - y ^ 2 = p ∧ 3 * x * y + p * (x - y) = p ^ 2} = {3} := by

  ext p 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Suppose p is a prime number with 0 < p and integer solutions
    intro h
    rcases h with ⟨h_prime, hp_pos, ⟨x, y, h1, h2⟩⟩

    have h_eq1 : p = (x - y) * (x + y) := by 
      nlinarith

    have h_eq2 : p ∣ 3 * (x * y) := by 
      have eq1 : 3 * (x * y) = p ^ 2 - p * (x - y) := by
        nlinarith [h2, h_eq1]
      have : p ∣ p ^ 2 - p * (x - y) := by
        use p - (x - y)
        ring_nf
        <;> nlinarith
      have : p ∣ 3 * (x * y) := by
        rw [eq1]
        exact this
      assumption

    have h_eq3 : p ∣ 3 ∨ p ∣ x ∨ p ∣ y := by 
      have h3 : p ∣ 3 * (x * y) := by assumption
      have h4 : p ∣ 3 ∨ p ∣ (x * y) := by
        apply (Prime.dvd_mul h_prime).mp at h3
        tauto
      rcases h4 with (h4 | h4)
      · -- Assume h4 : p ∣ 3
        left
        assumption
      · -- Assume h4 : p ∣ x * y
        have h5 : p ∣ x ∨ p ∣ y := by
          apply (Prime.dvd_mul h_prime).mp 
          assumption
        rcases h5 with (h5 | h5)
        · -- Assume h5 : p ∣ x
          right
          left
          assumption
        · -- Assume h5 : p ∣ y
          right
          right
          assumption

    rcases h_eq3 with (h3 | h3 | h3)
    · -- Assume h3 : p ∣ 3
      have h4 : p = 3 := by 
        have h5 : p ∣ 3 := h3
        have h6 : p ≤ 3 := by
          exact Int.le_of_dvd (by norm_num) h5
        have h7 : p ≥ 2 := by 
          by_contra h
          push_neg at h
          interval_cases p <;> norm_num at h_prime hp_pos
        interval_cases p <;> norm_num at h_prime hp_pos h5 <;> try tauto
      tauto

    · -- Assume h3 : p ∣ x
      have h4 : p ∣ x := h3
      -- Thus p divides $x$

      -- Since p divides x, so x ≡ 0 (mod p)
      -- From first equation: x^2 - y^2 = p
      -- So x^2 ≡ y^2 + p ≡ y^2 (mod p)
      -- So x^2 ≡ y^2 (mod p)
      -- Since p divides x, so x ≡ 0 (mod p)
      -- Then x^2 ≡ 0 ≡ y^2 (mod p)
      -- Therefore, y^2 ≡ 0 (mod p)
      -- Therefore, p divides y
      have h5 : p ∣ y := by 
        have h6 : p ∣ x ^ 2 - y ^ 2 := by
          use 1
          all_goals nlinarith
        have h7 : p ∣ x ^ 2 := by
          apply dvd_pow
          exact h4
          norm_num
        have h9 : p ∣ y ^ 2 := by 
          have h10 : x ^ 2 - y ^ 2 = p := h1
          have h11 : p ∣ x ^ 2 - y ^ 2 := by
            use 1
            all_goals nlinarith
          have h12 : p ∣ y ^ 2 := by
            have h13 : p ∣ x ^ 2 := h7
            have h14 : p ∣ (x ^ 2 - (x ^ 2 - y ^ 2)) := by
              apply Dvd.dvd.sub
              exact h13
              exact h11
            have h15 : x ^ 2 - (x ^ 2 - y ^ 2) = y ^ 2 := by
              nlinarith
            rw [h15] at h14
            exact h14
          exact h12
        have h11 : p ∣ y := by 
          apply Prime.dvd_of_dvd_pow h_prime
          exact h9
        assumption

      -- Substituting into the first equation: x^2 - y^2 = p
      -- Since p divides x and y
      -- Let x = m * p, Y = k * p
      -- So: (m p)^2 - (k p)^2 = p
      -- So: p^2 (m^2 -k^2) = p
      -- Divide by p (since p ≠ 0)
      -- p (m^2 -k^2) = 1
      -- So p divides 1
      -- But then p = 1 or p = -1
      -- But p is a positive prime
      -- Hence contradiction
      have h5 : p ∣ y := h5
      rcases h4 with ⟨m, hm⟩
      rcases h5 with ⟨k, hk⟩
      rw [hm, hk] at h1
      have h14 : p * (m ^ 2 - k ^ 2) = 1 := by 
        nlinarith 
      have h19 : p ∣ 1 := by
        use m ^ 2 - k ^ 2
        all_goals linarith
      have h20 : p ≤ 1 := by 
        exact Int.le_of_dvd (by norm_num) h19
      have h21 : p ≥ 2 := by 
        by_contra h
        push_neg at h
        interval_cases p <;> norm_num at h_prime hp_pos
      linarith

    · -- Assume h3 : p ∣ y
      have h4 : p ∣ y := h3
      -- Thus p divides $y$

      -- Since p divides y, so y ≡ 0 (mod p)
      -- From first equation: x^2 - y^2 = p
      -- So x^2 ≡ y^2 + p ≡ y^2 (mod p)
      -- So x^2 ≡ y^2 (mod p)
      -- Since p divides y, so y ≡ 0 (mod p)
      -- Then x^2 ≡ 0 ≡ y^2 (mod p)
      -- Therefore, x^2 ≡ 0 (mod p)
      -- Therefore, p divides x
      have h5 : p ∣ x := by
        have h6 : p ∣ x ^ 2 - y ^ 2 := by
          use 1
          all_goals nlinarith
        have h7 : p ∣ y ^ 2 := by
          apply dvd_pow
          exact h4
          norm_num
        have h8 : p ∣ x ^ 2 := by 
          have h9 : p ∣ (x ^ 2 - y ^ 2 + y ^ 2) := by 
            apply Dvd.dvd.add
            exact h6
            exact h7
          have h10 : x ^ 2 - y ^ 2 + y ^ 2 = x ^ 2 := by 
            nlinarith
          rw [h10] at h9
          exact h9
        have h9 : p ∣ x := by
          apply Prime.dvd_of_dvd_pow h_prime
          exact h8
        assumption

      -- Substituting into the first equation: x^2 - y^2 = p
      -- Since p divides x and y
      -- Let x = m * p, Y = k * p
      -- So: (m p)^2 - (k p)^2 = p
      -- So: p^2 (m^2 -k^2) = p
      -- Divide by p (since p ≠ 0)
      -- p (m^2 -k^2) = 1
      -- So p divides 1
      -- But then p = 1 or p = -1
      -- But p is a positive prime
      -- Hence contradiction
      have  h5 : p ∣ x  := h5
      rcases h4 with ⟨k, hk⟩
      rcases h5 with ⟨m, hm⟩
      rw [hm, hk] at h1
      have h14 : p * (m ^ 2 - k ^ 2) = 1 := by
        nlinarith
      have h19 : p ∣ 1 := by
        use m ^ 2 - k ^ 2
        all_goals linarith
      have h20 : p ≤ 1 := by 
        exact Int.le_of_dvd (by norm_num) h19
      have  h21 :  p ≥ 2 := by
        by_contra h
        push_neg at h
        interval_cases  p <;> norm_num at h_prime hp_pos
      linarith

  · -- Show that 3 satisfies
    intro h_eq
    rw [h_eq]
    constructor 
    · -- Show that 3 is prime
      norm_num
    constructor
    · -- Show that 0 < 3
      norm_num 
    · -- Show that there exists integer solutions
      use 2, 1
      constructor
      · -- Show that 2^2 - 1^2 = 3
        norm_num
      · -- Show that 3 * 2 * 1 + 3 * (2 - 1) = 3^2
        norm_num