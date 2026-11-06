import Mathlib
/- Does there exist an irrational number $\alpha>1$ such that

$$
\left\lfloor\alpha^{n}\right\rfloor \equiv 0 \quad(\bmod 2017)
$$

for all integers $n \geq 1$ ? -/
theorem algebra_609709 : ∃ a : ℝ, Irrational a ∧ a > 1 ∧ ∀ n : ℕ, n ≥ 1 → ⌊a ^ n⌋ ≡ 0 [ZMOD 2017]:= by
  -- We use the larger root of the quadratic equation x^2 - 4035x + 2017 = 0
  use ((4035 + √(4035 ^ 2 - 4 * 2017)) / 2)

  -- This lemma proves that if the square root of a natural number is rational,
  -- then it must be an integer
  have h1 : ∀ a : ℕ, (∃ r : ℚ, √a = r) → ∃ t : ℤ, √a = t:= by
    intro a h
    rcases h with ⟨r, hr⟩
    have h2:= Rat.mul_self_den r
    have h:= hr
    replace hr : √a ^ 2 = r ^ 2:= by rw [hr]
    field_simp at hr
    replace hr : a = r ^ 2:= by rify ; linarith
    have g2 : (↑a : ℚ).den = 1:= by exact rfl
    rw [show r * r = r ^ 2 by ring_nf] at h2
    rw [hr, h2] at g2
    simp at g2
    rw [show r = r.num / r.den by exact Eq.symm (Rat.num_div_den r)] at h
    rw [g2] at h
    simp at h
    use r.num

  constructor
  -- First part: Proving that our chosen number is irrational
  .
    by_contra H
    simp [Irrational] at H
    rcases H with ⟨r, hr⟩
    ring_nf at hr
    replace hr : √16273157 = 2 * r - 4035:= by linarith
    specialize h1 16273157 (⟨2 * r - 4035, by simp ; exact hr⟩)
    rcases h1 with ⟨t, ht⟩
    -- If √16273157 = t (an integer), then we derive a contradiction
    have ht0 : t > 0:= by
      rify
      rw [←ht]
      positivity
    have ht1 : t > 4034:= by
      by_contra H
      simp at H
      replace H : t ^ 2 ≤ 4034 ^ 2:= by nlinarith only [ht0, H]
      rify at H
      rw [←ht] at H
      field_simp at H
      linarith
    have ht2 : t < 4035:= by
      by_contra H
      simp at H
      replace H : t ^ 2 ≥ 4035 ^ 2:= by nlinarith only [H]
      rify at H
      rw [←ht] at H
      field_simp at H
      linarith
    linarith

  -- Second part: Proving that our number is > 1 and satisfies the floor condition
  .
    constructor
    -- Proving that our number is > 1
    .
      ring_nf
      have g1 : √16273157 > 0:= by positivity
      linarith

    -- Proving that the floor of a^n is divisible by 2017 for all n ≥ 1
    .
      -- Define a and b as the two roots of the quadratic equation
      set a:= (4035 + √(4035 ^ 2 - 4 * 2017)) / 2 with ha
      set b:= (4035 - √(4035 ^ 2 - 4 * 2017)) / 2 with hb
      clear_value a b

      -- Verify that a and b satisfy the quadratic equation
      have h2 : a ^ 2 - 4035 * a + 2017 = 0:= by
        rw [ha]
        ring_nf
        field_simp
      have h3 : b ^ 2 - 4035 * b + 2017 = 0:= by
        rw [hb]
        ring_nf
        field_simp

      -- Prove that 0 < b < 1
      have hb1 : b > 0:= by
        rw [hb]
        ring_nf
        have g1 : (16273157 : ℝ) < 4035 ^ 2:= by linarith
        have g2 : (16273157 : ℝ) ≥ 0:= by positivity
        replace g1 : √16273157 < √(4035 ^ 2):= by exact Real.sqrt_lt_sqrt g2 g1
        field_simp at g1
        linarith
      have hb2 : b < 1:= by
        rw [hb]
        ring_nf
        have g1 : (16273157 : ℝ) > 4034 ^ 2:= by linarith
        have g2 : (4034 : ℝ) ^ 2 ≥ 0:= by positivity
        replace g1 : √16273157 > √(4034 ^ 2):= by exact Real.sqrt_lt_sqrt g2 g1
        field_simp at g1
        linarith

      -- Prove that b^n is between 0 and 1 for all n > 0
      have hbn : ∀ n : ℕ, n > 0 → b ^ n > 0 ∧ b ^ n < 1:= by
        intro n hn
        constructor
        .
          positivity
        .
          refine pow_lt_one₀ (by linarith) hb2 (by omega)

      -- Define f(n) = a^n + b^n
      set f : ℕ → ℝ := fun n => a ^ n + b ^ n with hf
      clear_value f

      -- Prove that f satisfies a recurrence relation
      have g1 : ∀ n : ℕ, f (n + 2) - 4035 * f (n + 1) + 2017 * f n = 0:= by
        intro n
        simp [hf]
        rw [show a ^ (n + 2) = a ^ n * a ^ 2 by ring_nf]
        rw [show b ^ (n + 2) = b ^ n * b ^ 2 by ring_nf]
        rw [show a ^ (n + 1) = a ^ n * a by ring_nf]
        rw [show b ^ (n + 1) = b ^ n * b by ring_nf]
        replace h2 : a ^ n * (a ^ 2 - 4035 * a + 2017) + b ^ n * (b ^ 2 - 4035 * b + 2017) = 0:= by rw [h2, h3] ; simp
        linarith

      -- Prove that f(n) is always an integer
      have hfn : ∀ n : ℕ, (∃ k1 : ℤ, f n = k1) ∧ (∃ k2 : ℤ, f (n + 1) = k2):= by
        intro n
        induction n with
        | zero =>
          simp [hf]
          constructor
          .
            use 2
            simp
            linarith
          .
            use 4035
            rw [ha, hb]
            simp
            linarith
        | succ n hn =>
          rcases hn with ⟨hn1, hn2⟩
          constructor
          .
            exact hn2
          .
            rw [show n + 1 + 1 = n + 2 by ring_nf]
            specialize g1 n
            rcases hn1 with ⟨k1, hk1⟩
            rcases hn2 with ⟨k2, hk2⟩
            use (4035 * k2 - 2017 * k1)
            rw [hk1, hk2] at g1
            simp
            linarith

      -- Prove that ⌊a^n⌋ = a^n + b^n - 1 for all n > 0
      have hn : ∀ n : ℕ, n > 0 → ⌊a ^ n⌋ = a ^ n + b ^ n - 1:= by
        intro n hn
        specialize hfn n
        replace hfn:= hfn.1
        rcases hfn with ⟨k1, hk1⟩
        simp [hf] at hk1
        rw [hk1]
        specialize hbn n hn
        rcases hbn with ⟨hbn1, hbn2⟩
        rw [show a ^ n = a ^ n - k1 + 1 + (k1 - 1) by ring_nf]
        set t:= a ^ n - k1 + 1 with ht
        clear_value t
        replace g1 : t ≥ 0:= by linarith
        replace g2 : t < 1:= by linarith
        rw [show (↑k1 : ℝ) - 1 = (k1 - 1 : ℤ) by simp]
        rw [show ↑⌊t + ↑(k1 - 1)⌋ = ⌊t⌋ + ↑(k1 - 1) by exact Int.floor_add_int t (k1 - 1)]
        simp
        exact ⟨g1, g2⟩

      -- Prove that f(n) ≡ 1 (mod 2017) for all n ≥ 1
      replace hfn : ∀ n : ℕ, (∃ k1 : ℤ, f (n + 1) = 2017 * k1 + 1) ∧ (∃ k2 : ℤ, f (n + 2) = 2017 * k2 + 1):= by
        intro n
        induction n with
        | zero =>
          simp [hf]
          rw [ha, hb]
          ring_nf
          field_simp
          ring_nf
          constructor
          .
            use 2
            simp
            linarith
          .
            use 8070
            simp
            linarith
        | succ n hn =>
          rw [show n + 1 + 1 = n + 2 by ring_nf]
          rw [show n + 1 + 2 = n + 3 by ring_nf]
          rcases hn with ⟨hn1, hn2⟩
          constructor
          .
            exact hn2
          .
            specialize g1 (n + 1)
            rw [show n + 1 + 2 = n + 3 by ring_nf] at g1
            rw [show n + 1 + 1 = n + 2 by ring_nf] at g1
            rcases hn1 with ⟨k1, hk1⟩
            rcases hn2 with ⟨k2, hk2⟩
            use (2017 * 2 * k2 - 2017 * k1 + 1 + k2)
            rw [hk1, hk2] at g1
            simp
            linarith

      -- Final proof: ⌊a^n⌋ ≡ 0 (mod 2017) for all n ≥ 1
      intro n hnn
      specialize hn n hnn
      specialize hfn (n - 1)
      rw [show n - 1 + 1 = n by omega] at hfn
      replace hnf:= hfn.1
      rcases hnf with ⟨k1, hk1⟩
      simp [hf] at hk1
      rw [hk1] at hn
      ring_nf at hn
      replace hn : ⌊a ^ n⌋ = k1 * 2017:= by
        rify
        linarith
      rw [hn]
      have hgoal : 2017 ≡ 0 [ZMOD 2017]:= by rfl
      replace hgoal : k1 * 2017 ≡ k1 * 0 [ZMOD 2017]:= by exact Int.ModEq.mul_left k1 hgoal
      simp at hgoal
      exact hgoal
