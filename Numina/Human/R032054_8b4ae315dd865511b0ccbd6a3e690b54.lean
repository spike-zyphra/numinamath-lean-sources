import Mathlib


/- For how many real values of x is sqrt(120-sqrt(x)) an integer?
(A) 3
(B) 6
(C) 9
(D) 10
(E) 11 -/
theorem algebra_96075 : {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n^2 = 120 - Real.sqrt x}.ncard = 11 := by
  -- a lemma that square equal means value equal for naturals, will be used later
  have sq_inj {a b: ℕ} (hab: a^2 = b^2) : a = b := by
    refine (pow_left_inj₀ ?_ ?_ (by norm_num: 2 ≠ 0)).mp ?_
    all_goals linarith
  -- n^2 ≤ 120 iff n ≤ 10 for naturals, will be used later
  have hn_ineq {n : ℕ} : n^2 ≤ 120 ↔ n ≤ 10 := by
    constructor
    all_goals intro hn
    . suffices h: n^2 < 11^2 by
        have : n < 11 := lt_of_pow_lt_pow_left' 2 h
        omega
      linarith
    . suffices h: n^2 ≤ 10^2 by linarith
      refine Nat.pow_le_pow_of_le_left hn 2
  -- define f (n) = (120 - n^2)^2, the function that'll be injective on [0, 10] to the target set, prove it is ijective using lemmas
  let f (n: ℕ) : ℝ := (120 - n^2)^2
  have finj : Set.InjOn f (Set.Icc 0 10) := by
    rintro a ⟨ha₁, ha₂⟩ b ⟨hb₁, hb₂⟩ fab
    dsimp [f] at fab
    have ⟨ha₃, hb₃⟩ : a^2 ≤ 120 ∧ b^2 ≤ 120 := by
      constructor
      . exact hn_ineq.mpr ha₂
      . exact hn_ineq.mpr hb₂
    norm_cast at fab
    have : 120 - a ^ 2 = 120 - b ^ 2 := sq_inj fab
    have : a^2 = b^2 := by omega
    exact sq_inj this
  -- now prove target set is f([0, 10])
  have h: {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n^2 = 120 - Real.sqrt x} = f '' Set.Icc 0 10 := by
    ext x
    constructor
    -- prove if x in target set then there is f(n) = x with n in [0, 10]
    . rintro ⟨n, hx, hnx⟩
      use n
      constructor
      any_goals constructor
      . linarith
      . suffices h: n^2 ≤ 120 by exact hn_ineq.mp h
        rify
        have : 0 ≤ √x := by simp
        linarith
      . dsimp [f]
        rw [hnx]
        ring_nf
        simp [hx]
    -- prove if f(n) = x with n in [0, 10] then x in target set
    . rintro ⟨n, ⟨⟨hn₁,hn₂⟩, hf⟩⟩
      use n
      dsimp [f] at hf
      constructor
      . rw [← hf]
        exact sq_nonneg _
      . rw [← hf]
        have : 0 ≤  120 - (n:ℝ) ^ 2 := by
          have := hn_ineq.mpr hn₂
          norm_cast
          linarith
        simp [this]
  -- finally prove cardinality is 11
  calc
    {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n^2 = 120 - Real.sqrt x}.ncard = (f '' Set.Icc 0 10).ncard := by rw [h]
    _ = (Set.Icc 0 10).ncard := by exact Set.ncard_image_of_injOn finj
    _ = Nat.card (Set.Icc 0 10) := by rw[Set.Nat.card_coe_set_eq]
    _ = 11 := by simp