import Mathlib

/- Trouver toutes les valeurs possibles pour $f(2018)$ où $f$ est une fonction de $\mathbb{Q}$ dans $\mathbb{R}_{+}$vérifiant les trois conditions suivantes:

- $f(2)=1 / 2$ ；
- pour tout rationnel $x$, si $f(x) \leqslant 1$, alors $f(x+1) \leqslant 1$;
- $f(x y)=f(x) f(y)$ pour tous rationnels $x$ et $y$. -/
theorem algebra_605467  (F : Set (ℚ → ℝ))
  (hF : F = {f |
    (∀ x, f x ≥ 0) ∧
    (f 2 = 1 / 2) ∧
    (∀ x, f x ≤ 1 → f (x + 1) ≤ 1) ∧
    (∀ x y, f (x * y) = f x * f y)})
  : {f 2018 | f ∈ F} = {1 / 2} := by
  -- we formulate the problem in the form of sets
  -- note that f should actually be a function from ℚ to ℝ_≥0 instead of ℝ+,
  -- because we must have f(0) = 0.

  -- first we show that any function satisfying those conditions must have f(2018) = 1 / 2
  have left_in_right : ∀ f ∈ F, f 2018 = 1 / 2 := by
    -- let f be a function satisfying those conditions.
    intro f f_mem
    rw [hF] at f_mem
    have ⟨hf₀, hf₁, hf₂, hf₃⟩ := f_mem

    -- we deduce f(x) ≠ 0 whenever x ≠ 0, because 0 ≠ f(2) = f(2/x * x) = f(2/x) * f(x)
    have f_nz : ∀ x ≠ 0, f x ≠ 0 := by
      by_contra! h
      obtain ⟨x, hx, hfx⟩ := h
      have : (2 : ℚ) = 2 / x * x := Eq.symm (div_mul_cancel₀ 2 hx)
      rw [this, hf₃, hfx] at hf₁
      simp at hf₁

    -- we deduce f(1) = f(1) * f(2) / f(2) = f(1 * 2) / f(2) = f(2) / f(2) = 1
    have f_1_eq_1 : f 1 = 1 := by
      calc
        f 1 = f 1 * f 2 / f 2 := by field_simp
        _ = f (1 * 2) / f 2 := by congr; symm; exact hf₃ 1 2
        _ = f 2 / f 2 := by congr; ring
        _ = 1 := by field_simp

    -- so by induction, for all positive natural number n > 0, we have f(n) ≤ 1
    have f_n_le_1 : ∀ n : ℕ, n > 0 → f n ≤ 1 := by
      intro n
      induction' n with n ih
      · simp
      · by_cases h : n > 0
        · intros
          rw [Nat.cast_add]
          simp
          exact hf₂ (↑n) (ih h)
        · have : n = 0 := by linarith
          rw [this]; simp [f_1_eq_1]

    -- we also deduce f(x / y) = f(x) / f(y) if y ≠ 0
    have f_div : ∀ x y, y ≠ 0 → f (x / y) = f x / f y := by
      intro x y ynz
      have : f y ≠ 0 := f_nz y ynz
      field_simp
      rw [← hf₃ (x / y) y]
      congr; field_simp

    -- therefore f(1/2) = f(1) / f(2) = 2
    have f_half_eq_2 : f (1 / 2) = 2 := by
      rw [f_div 1 2 (by norm_num), f_1_eq_1, hf₁]
      norm_num

    -- we show that f is non-decreasing on odd numbers
    have f_odd_inc : ∀ n : ℤ, (n ≥ 0) → f (2 * n - 1) ≤ f (2 * n + 1) := by
      intro n npos
      let k := 2 * n + 1  -- let k = 2n + 1 be odd
      -- so k ≠ 0, f(k) ≠ 0, and thus f(k) > 0
      have knz : k ≠ 0 := by
        have : Odd k := by exact odd_two_mul_add_one n
        by_contra! h
        rw [h] at this
        norm_num at this
      have fknz : f k ≠ 0 := by
        apply f_nz
        norm_cast
      have fk_pos : f k > 0 := by
        have := hf₀ k
        exact lt_of_le_of_ne (hf₀ ↑k) (id (Ne.symm fknz))

      -- also, -k/2 ≠ 0, so f(-k/2) > 0
      have fk2_nz : f (-k / 2) ≠ 0 := by
        apply f_nz
        simp [knz]
      have fk2_pos : f (-k / 2) > 0 := by
        have := hf₀ (-k / 2)
        exact lt_of_le_of_ne (hf₀ (-↑k / 2)) (id (Ne.symm fk2_nz))

      -- it suffices to show that f(k - 2) ≤ f(k), i.e. f(k-2 / k) ≤ 1, i.e. f(-2/k + 1) ≤ 1
      suffices h : f (k - 2) ≤ f k by
        unfold k at h
        norm_cast at h ⊢
        rw [show (2 * n + 1 - 2) = 2 * n - 1 by ring] at h
        linarith
      suffices h : f (k - 2) / f k ≤ 1 by
        exact (div_le_one₀ fk_pos).mp h
      have : f k ≠ 0 := by apply f_nz; norm_cast

      rw [← f_div _ _ (by norm_cast)]
      rw [show (k - 2 : ℚ) / k = -2 / k + 1 by field_simp; ring]

      -- using the property of f, we turn to show f(-2/k) ≤ 1
      apply hf₂

      -- equivalently, 1 / f(-k/2) ≤ 1
      rw[show (-2 /k : ℚ) = 1 / (-k / 2) by field_simp [knz]]
      rw [f_div _ _ (by simp [knz])]
      rw [f_1_eq_1]

      -- equivalently, f(-k/2) ≥ 1
      suffices h : f (-↑k / 2) ≥ 1 by
        exact (div_le_one₀ fk2_pos).mpr h
      suffices h : f (-↑k / 2) > 1 by linarith

      -- if on the contrary, f(-k/2) < 1, then 2 = f(1 / 2) = f(-↑k / 2 + (n + 1)) ≤ 1, contradiction
      by_contra! h
      have f_half_eq : f (1 / 2) = f (-↑k / 2 + (n + 1)) := by
        congr; unfold k; field_simp; ring

      let n' := n.natAbs
      have : n' = n := by exact Int.natAbs_of_nonneg npos
      rw [← this] at f_half_eq

      have : f (-k / 2 + (n' + 1)) ≤ 1 := by
        induction' n' with n' ih
        · simp
          exact hf₂ (-↑k / 2) h
        · rw [← add_assoc]
          apply hf₂
          rw [Nat.cast_add]
          simp [ih]

      have : f (1 / 2) ≤ 1 := by
        rw [f_half_eq]
        norm_cast at this ⊢
      have : f (1 / 2) > 1 := by linarith
      linarith

    -- so for all odd numbers 2n + 1, we have f(2n + 1) ≥ 1
    have f_odd_ge_1 : ∀ n : ℕ, f (2 * n + 1) ≥ 1 := by
      rw [← f_1_eq_1]
      intro n
      induction' n with n ih
      · simp
      · have := f_odd_inc (n + 1) (by linarith)
        rw [Int.cast_add] at this
        rw [Nat.cast_add]
        nth_rw 1 [mul_add] at this
        simp [show (2 * ↑n + 2 - 1 : ℚ) = 2 * ↑n + 1 by ring] at this ⊢
        linarith

    -- combining previous results, for all odd numbers 2n + 1, we have f(2n + 1) = 1
    have f_odd_eq_1 : ∀ n : ℕ, f (2 * n + 1) = 1 := by
      intro n
      have := f_odd_ge_1 n
      have := f_n_le_1 (2 * n + 1) (by linarith)
      norm_cast at *
      linarith

    -- so f(2018) = f(2)f(1009) = 1/2
    rw [show (2018 : ℚ) = 2 * 1009 by norm_num]
    rw [hf₃, hf₁]
    rw [show (1009 : ℚ) = 2 * (504 : ℕ) + 1 by norm_num]
    rw [f_odd_eq_1]
    simp

  ext
  constructor
  ·
    simp
    intro f hf
    suffices h : f 2018 = 1 / 2 by intro a; subst a; simp [h]
    exact left_in_right f hf

  · -- we are left to show that there is indeed a function f satisfying the conditions in the problem
    simp

    -- we explicitly construct f(x) = if x = 0 then 0 else (2 ^ (-v₂(x)), where v₂(x) is the 2-adic valuation of x
    let f : ℚ → ℝ := fun x ↦ if x = 0 then 0 else (2 ^ (-padicValRat 2 x : ℝ))
    intros
    use f

    have f_mem : f ∈ F := by
      rw [hF]
      simp
      constructor
      · -- 1. we show f(x) ≥ 0 for all x, this is routine
        intro x
        unfold f
        by_cases h : x = 0
        · simp [h]
        simp [h]
        apply Real.rpow_nonneg
        norm_num
      constructor
      · -- 2. we calculate f(2) = 2^-1 = 1/2
        unfold f
        have : padicValRat 2 2 = 1 := by
          apply padicValRat.self
          norm_num
        rw [this]
        norm_num
      constructor
      · -- 3. we show that f(x) ≤ 1 implies f(x + 1) ≤ 1
        -- here we need to use the fact that v₂(x + 1) ≥ min(v₂(x), v₂(1))
        intro x
        by_cases h1 : x = 0
        · rw [h1]
          intro _
          unfold f
          simp
        by_cases h2 : x + 1 = 0
        · rw [h2]
          intro _
          unfold f
          simp
        simp [h1, h2, f]
        intro le

        rw [Real.rpow_le_one_iff_of_pos (show 2 > 0 by norm_num)] at le
        simp at le

        rw [Real.rpow_le_one_iff_of_pos (show 2 > 0 by norm_num)]
        simp

        have := padicValRat.min_le_padicValRat_add (p := 2) h2
        simp [le] at this
        exact this

      -- 4. finally we show f(xy) = f(x)f(y), because v₂(xy) = v₂(x)v₂(y)
      intro x y
      unfold f
      by_cases h1 : x = 0
      · simp [h1]
      by_cases h2 : y = 0
      · simp [h2]
      simp [h1, h2]
      rw [padicValRat.mul]
      simp
      rw [Real.rpow_add, mul_comm]
      norm_num
      assumption
      assumption

    use f_mem
    simp_all
