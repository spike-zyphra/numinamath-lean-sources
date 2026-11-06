import Mathlib

/- 23. (YUG 2) Prove that for every natural number $k(k \geq 2)$ there exists an irrational number $r$ such that for every natural number $m$,  $$ \left[r^{m}\right] \equiv-1 \quad(\bmod k) $$  Remark. An easier variant: Find $r$ as a root of a polynomial of second degree with integer coefficients. -/
theorem number_theory_24088 (k : ℕ) (hk : 2 ≤ k) :
    ∃ r : ℝ, Irrational r ∧ ∀ m : ℕ, (1 ≤ m) → Int.floor (r ^ m) ≡ -1 [ZMOD k] := by
  -- We'll find a quadratic polynomial with specific coefficients.
  -- Specifically, we'll set p = 3 and q = 2 for our polynomial f(x) = x² - kp·x + kq
  let b : ℝ := 3 * k
  let c : ℝ := 2 * k
  -- The polynomial has a root between 0 and 1, because f(0) > 0 > f(1).
  obtain ⟨s, hs1, hs2, hs3⟩ : ∃ s : ℝ, s * s - b * s + c = 0 ∧ 0 < s ∧ s < 1 := by
    let f : ℝ → ℝ := fun x ↦ x * x - b * x + c
    have h1 := intermediate_value_Ioo' (show (0 : ℝ) ≤ 1 by simp) (f := fun x ↦ x * x - b * x + c) (by fun_prop)
    simp at h1
    have h2 : 0 ∈ Set.Ioo (1 - b + c) c := by
      simp [b, c]
      constructor
      · rify at hk
        linarith
      · linarith
    apply h1 at h2
    simp at h2
    obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ := h2
    use s
  -- By Vieta's formulas, if s is one root, there exists another root r with r·s = c and r+s = b
  obtain ⟨r, hr1, h2, h3⟩ := vieta_formula_quadratic hs1
  simp [b, c] at h2 h3
  rw [add_comm] at h2
  rw [mul_comm] at h3
  -- Now we prove that r^m + s^m ≡ 0 (mod k) for all m ≥ 1 using induction on m.
  -- This follows from the fact that r+s ≡ 0 (mod k) and r·s ≡ 0 (mod k)
  have h4 : ∀ (m : ℕ), 1 ≤ m → ∃ (n : ℤ), (r^m + s^m) = n ∧ n ≡ 0 [ZMOD k] := by
    intro m hm
    induction' m using Nat.strong_induction_on with m ih
    cases' m with m
    · simp at hm
    cases' m with m
    · use 3 * k
      simp [h2, Int.modEq_zero_iff_dvd]
    have h5 : r ^ (m + 2) + s ^ (m + 2) = (r^(m + 1) + s^(m + 1)) * (r + s) - r * s * (r^m + s^m) := by
      ring_nf
    simp_rw [h5, h2, h3]
    cases' m with m
    · simp [h2, h3]
      use 3 * k * (3 * k) - 2 * k * (1 + 1)
      norm_num
      trans k * (3 * (3 * ↑k) - 2 * 2)
      · congr
        ring
      simp [Int.modEq_zero_iff_dvd]
    obtain ⟨u, hu1, hu2⟩ := ih (m + 1) (by omega) (by omega)
    obtain ⟨v, hv1, hv2⟩ := ih (m + 2) (by omega) (by omega)
    use v * (3 * k) - 2 * k * u
    simp [hu1, hv1]
    trans k * (v * 3 - 2 * u)
    · congr
      ring
    simp [Int.modEq_zero_iff_dvd]
  use r
  constructor
  swap
  -- For any m ≥ 1, we need to show that ⌊r^m⌋ ≡ -1 (mod k)
  -- This follows from the fact that r^m + s^m ≡ 0 (mod k) and 0 < s^m < 1
  · intro m hm
    specialize h4 m hm
    obtain ⟨n, hn1, hn2⟩ := h4
    have : ⌊r ^ m⌋ = n - 1 := by
      replace hn1 : r^m = n - s^m := by linarith
      rw [hn1]
      rw [Int.floor_eq_iff]
      constructor
      · simp
        suffices s^m < 1 by linarith
        apply pow_lt_one₀
        · linarith
        · linarith
        · omega
      · simp
        exact pow_pos hs2 m
    rw [this]
    trans 0 - 1
    · exact Int.ModEq.sub_right _ hn2
    · simp
  -- Finally, we prove that r is irrational
  -- This corresponds to showing that the discriminant D is not a perfect square
  · let D := discrim 1 (-b) c
    let s := √D
    have hD_pos : 4 * (2 * k) ≤ (3 * k) ^ 2 := by
      nlinarith
    have hD_nat : D = ((3 * k) ^ 2 - 4 * (2 * k) : ℕ) := by
      simp [D, discrim, b, c]
      rify [hD_pos]
    have hDs : D = s * s := by
      refine Eq.symm (Real.mul_self_sqrt ?_)
      simp [D, discrim, b, c]
      rify at hD_pos
      exact hD_pos
    have := quadratic_eq_zero_iff (show (1 : ℝ) ≠ 0 by simp) hDs r |>.mp (by linarith)
    simp at this
    suffices hs : Irrational s by
      rcases this with this | this <;>
      rw [this, show (2 : ℝ) = (2 : ℕ) by simp] <;>
      apply Irrational.div_nat _ (by norm_num) <;> simp [b] <;>
      rw [show (3 * k : ℝ) = (3 * k : ℕ) by simp]
      · apply Irrational.nat_add hs
      · apply Irrational.nat_sub hs
    simp [s, hD_nat]
    rw [irrational_sqrt_natCast_iff]
    set D := (3 * k) ^ 2 - 4 * (2 * k)
    clear hD_nat hDs
    -- The discriminant is bounded: (3k-2)² < D < (3k-1)²
    -- This shows D is not a perfect square, proving r is irrational
    have hD1 : (3 * k - 2)^2 < D := by
      have : 3 * k > 2 := by omega
      zify [this]
      simp [D]
      push_cast [hD_pos]
      linarith
    have hD2 : D < (3 * k - 1)^2 := by
      have : 3 * k > 1 := by omega
      zify [this]
      simp [D]
      push_cast [hD_pos]
      linarith
    intro ⟨d, hd⟩
    replace hd : D = d^2 := by linarith
    rw [hd] at hD1 hD2
    rw [sq_lt_sq₀] at hD1 hD2
    · omega
    all_goals simp
