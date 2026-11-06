import Mathlib

/- There are $20n$ members in the Trumpington marching band, and when they line up in rows of 26, there are 4 band members left over. If $n$ is an integer and there are fewer than 1000 band members, what is the maximum number of people that could be in the Trumpington marching band? -/
theorem number_theory_15865 : IsGreatest {k : ℕ | 20 ∣ k ∧ k % 26 = 4 ∧ k < 1000} 940 := by
  -- Two goals: show 940 satisfies the conditions and is the largest
  constructor
  . -- Show 940 satisfies the conditions
    simp
    -- Show 20 ∣ 940 by showing 940 = 20 * 47
    use 47
  . rintro k ⟨⟨n, rfl⟩, h1, h2⟩

    -- Replace h2 by n < 50
    have hb : n < 50 := by omega
    -- The goal is equivalent to n ≤ 47
    suffices _ : n ≤ 47 by omega

    -- Rewrite 20n % 26 = 4 as 20n ≡ 4 [MOD 26]
    -- And further as 4 * 5n ≡ 4 * 1 [MOD 26]
    change 4 * 5 * n ≡ 4 * 1 [MOD 26] at h1
    rw [mul_assoc] at h1

    -- Thus 5n ≡ 1 [MOD 26 / gcd 26 4]
    -- That is, 5n ≡ 1 [MOD 13]
    apply Nat.ModEq.cancel_left_div_gcd (show 0 < 26 by simp) at h1
    simp at h1

    -- Multiply 8 on both sides
    -- 40n ≡ 8 [MOD 13]
    apply Nat.ModEq.mul_left 8 at h1
    rw [← mul_assoc] at h1
    simp at h1

    -- Because 40 ≡ 1 [MOD 13], we have 40n ≡ n [MOD 13]
    -- Thus n ≡ 8 [MOD 13]
    have h3 : n ≡ 40 * n [MOD 13] := by
      rw [Nat.modEq_iff_dvd]
      omega
    have h : n ≡ 8 [MOD 13] := h3.trans h1
    clear h1 h2 h3

    -- n % 13 = 8
    change n % 13 = 8 at h
    rw [← Nat.mod_add_div n 13]

    -- Now the goal is equivalent to n / 13 ≤ 3
    suffices _ : n / 13 ≤ 3 by omega

    -- Which is clear from n < 50
    omega
