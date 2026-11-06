import Mathlib
/- The fraction $\frac{1}{2015}$ has a unique "(restricted) partial fraction decomposition" of the form

$$
\frac{1}{2015}=\frac{a}{5}+\frac{b}{13}+\frac{c}{31}
$$

where $a, b, c$ are integers with $0 \leq a<5$ and $0 \leq b<13$. Find $a+b$. -/
theorem algebra_609355 (a b c : ℤ) (ha : 0 ≤ a ∧ a < 5) (hb : 0 ≤ b ∧ b < 13) (h : (1 : ℝ) / 2015 = a / 5 + b / 13 + c / 31) : a + b = 14:= by
  -- Simplify the fraction equation
  field_simp at h
  -- Convert to integer equation: 403a + 155b + 65c = 1
  replace h : 403 * a + 155 * b + 65 * c = 1:= by
    rify
    linarith

  -- Apply modular arithmetic mod 5 and mod 13
  have h1 : 403 * a + 155 * b + 65 * c ≡ 1 [ZMOD 5] := by rw [h]
  have h2 : 403 * a + 155 * b + 65 * c ≡ 1 [ZMOD 13] := by rw [h]

  -- Establish that 65 is congruent to 0 mod 5 and mod 13
  have h3 : 65 ≡ 0 [ZMOD 5]:= by rfl
  have h4 : 65 ≡ 0 [ZMOD 13]:= by rfl
  replace h3 : 65 * c ≡ 0 * c [ZMOD 5]:= by exact Int.ModEq.mul h3 rfl
  replace h4 : 65 * c ≡ 0 * c [ZMOD 13]:= by exact Int.ModEq.mul h4 rfl
  simp at h3 h4

  -- Show that 155 ≡ 0 (mod 5) and 403 ≡ 0 (mod 13)
  have h5 : 155 ≡ 0 [ZMOD 5]:= by rfl
  have h6 : 403 ≡ 0 [ZMOD 13]:= by rfl
  replace h5 : 155 * b ≡ 0 * b [ZMOD 5]:= by exact Int.ModEq.mul h5 rfl
  replace h6 : 403 * a ≡ 0 * a [ZMOD 13]:= by exact Int.ModEq.mul h6 rfl
  simp at h5 h6

  -- Combine congruences using addition
  replace h3 : 65 * c + 155 * b ≡ 0 + 0 [ZMOD 5]:= by exact Int.ModEq.add h3 h5
  replace h4 : 65 * c + 403 * a ≡ 0 + 0 [ZMOD 13]:= by exact Int.ModEq.add h4 h6
  simp at h3 h4

  -- Subtract congruences to isolate terms
  replace h1 : 403 * a + 155 * b + 65 * c - (65 * c + 155 * b) ≡ 1 - 0 [ZMOD 5]:= by exact Int.ModEq.sub h1 h3
  replace h2 : 403 * a + 155 * b + 65 * c - (65 * c + 403 * a) ≡ 1 - 0 [ZMOD 13]:= by exact Int.ModEq.sub h2 h4

  -- Simplify expressions using ring arithmetic
  rw [show 403 * a + 155 * b + 65 * c - (65 * c + 155 * b) = 403 * a by ring] at h1
  rw [show 403 * a + 155 * b + 65 * c - (65 * c + 403 * a) = 155 * b by ring] at h2
  simp at h1 h2
  clear h3 h4 h5 h6

  -- Establish key congruences
  have h3 : 1 ≡ 806 [ZMOD 5]:= by rfl
  have h4 : 1 ≡ 155 * 12 [ZMOD 13]:= by rfl
  replace h1 : 403 * a ≡ 806 [ZMOD 5]:= by exact Int.ModEq.trans h1 h3
  replace h2 : 155 * b ≡ 155 * 12 [ZMOD 13]:= by exact Int.ModEq.trans h2 h4
  clear h3 h4

  -- Convert congruences to divisibility statements
  replace h1 : 5 ∣ (403 * a - 806):= by exact Int.ModEq.dvd (id (Int.ModEq.symm h1))
  replace h2 : 13 ∣ (155 * b - 155 * 12):= by exact Int.ModEq.dvd (id (Int.ModEq.symm h2))

  -- Factor out common terms
  rw [show 403 * a - 806 = 403 * (a - 2) by ring] at h1
  rw [show 155 * b - 155 * 12 = 155 * (b - 12) by ring] at h2

  -- Prove 5 and 13 are prime
  have h3 : Nat.Prime 5:= by norm_num
  have h4 : Nat.Prime 13:= by norm_num

  -- Apply prime divisibility properties
  replace h1 : (5 : ℤ) ∣ 403 ∨ 5 ∣ a - 2:= by refine Prime.dvd_or_dvd (by exact Int.prime_iff_natAbs_prime.mpr h3) h1
  replace h2 : (13 : ℤ) ∣ 155 ∨ 13 ∣ b - 12:= by refine Prime.dvd_or_dvd (by exact Int.prime_iff_natAbs_prime.mpr h4) h2

  -- Prove 403 is not divisible by 5 and 155 is not divisible by 13
  have h3 : ¬((5 : ℤ) ∣ 403):= by
    by_contra H
    omega
  have h4 : ¬((13 : ℤ) ∣ 155):= by
    by_contra H
    omega
  simp [h3] at h1
  simp [h4] at h2

  -- Use bounds on a and b to complete the proof
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  replace h1 : ∃ k : ℤ, a - 2 = 5 * k:= by exact h1
  rcases h1 with ⟨k1, hk1⟩
  replace h2 : ∃ k : ℤ, b - 12 = 13 * k:= by exact h2
  rcases h2 with ⟨k2, hk2⟩
  clear h3 h4
  have h3 : k1 = 0:= by omega
  have h4 : k2 = 0:= by omega
  subst k1 k2
  simp at hk1 hk2
  linarith
