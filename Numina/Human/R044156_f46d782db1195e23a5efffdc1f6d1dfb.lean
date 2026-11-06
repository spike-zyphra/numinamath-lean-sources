import Mathlib

open Polynomial
/- Let $m$ and $n$ be positive integers such that the equation $x^{2}-m x+n=0$ has real roots $\alpha$ and $\beta$. Prove that $\alpha$ and $\beta$ are integers if and only if $[m \alpha]+[m \beta]$ is the square of an integer. (Here $[x]$ denotes the largest integer not exceeding $x$.) -/
theorem algebra_607829 {m n : ℤ} (hm : m > 0) (hn : n > 0) (α β : ℝ) (h₀ : (X - C α) * (X - C β) = X ^ 2 - C (m : ℝ) * X + C (n : ℝ)) :
    (∃ a b : ℤ, α = a ∧ β = b) ↔ IsSquare (⌊m * α⌋ + ⌊m * β⌋) := by
  -- Break the goal into two parts.
  apply Iff.intro
  . -- First show that if α, β are integers, then ⌊m * α⌋ + ⌊m * β⌋ is a perfect square.
    rintro ⟨a, b, rfl, rfl⟩
    -- Show that m = a + b.
    have h₁ : m = a + b := by
      -- Basically this is because the sum of the roots is m.
      ring_nf at h₀
      rw [<-Polynomial.coeff_inj] at h₀
      replace h₀ := congr_arg (· 1) h₀
      simp at h₀
      simp [Mathlib.Tactic.ComputeDegree.coeff_intCast_ite] at h₀
      rify
      linarith only [h₀]
    -- Now ⌊m * α⌋ + ⌊m * β⌋ = m².
    use m
    norm_cast
    iterate 2 rw [Int.floor_intCast]
    nlinarith
  . -- Now show the opposite direction that if ⌊m * α⌋ + ⌊m * β⌋ is a perfect square, then α, β are integers.
    intro h₁
    -- Again, observe from comparing coefficients that m = α + β and n = αβ.
    have hm' : m = α + β := by
      ring_nf at h₀
      rw [<-Polynomial.coeff_inj] at h₀
      replace h₀ := congr_arg (· 1) h₀
      simp at h₀
      simp [Mathlib.Tactic.ComputeDegree.coeff_intCast_ite] at h₀
      linarith only [h₀]
    have hn' : n = α * β := by
      replace h₀ := congr_arg (Polynomial.eval (0 : ℝ) ·) h₀
      simp at h₀
      exact h₀.symm
    -- Let k² = ⌊m * α⌋ + ⌊m * β⌋. Make sure that k is natural number.
    obtain ⟨k', h₁⟩ := h₁
    let k := k'.natAbs
    rw [show k' * k' = k ^ 2 by simp [k, pow_two]] at h₁
    rify at h₁
    -- Note that m² - 2 < k² ≤ m².
    have h₂ : m ^ 2 - 2 < k ^ 2 := by
      rify
      calc
        (m ^ 2 - 2 : ℝ) = m * α - 1 + (m * β - 1) := by
          rw [hm']
          ring
        _ < ⌊m * α⌋ + ⌊m * β⌋ := by
          apply add_lt_add
          <;> apply Int.sub_one_lt_floor
        _ = k ^ 2 := h₁
    have h₃ : k ^ 2 ≤ m ^ 2 := by
      rify
      calc
        (k ^ 2 : ℝ) = ⌊m * α⌋ + ⌊m * β⌋ := h₁.symm
        _ ≤ m * α + m * β := by
          apply add_le_add
          <;> apply Int.floor_le
        _ = m ^ 2 := by
          rw [hm']
          ring
    -- Note first that α ≠ 0 and β ≠ 0.
    have h₄ : α ≠ 0 ∧ β ≠ 0 := by
      by_contra h₄
      rw [<-or_iff_not_and_not] at h₄
      obtain h₄ | h₄ := h₄
      all_goals
        simp [h₄] at hn'
        simp [hn'] at hn
    -- Note further that α, β > 0, because only this case would give m, n > 0.
    replace h₄ : α > 0 ∧ β > 0 := by
      iterate 2 rw [ne_iff_lt_or_gt] at h₄
      replace h₄ : (α < 0 ∧ β < 0) ∨ (α < 0 ∧ β > 0) ∨ (α > 0 ∧ β < 0) ∨ (α > 0 ∧ β > 0) := by
        tauto
      obtain h₄ | h₄ | h₄ | h₄ := h₄
      all_goals
        rify at hm hn
        first | tauto | nlinarith
    obtain ⟨h₄α, h₄β⟩ := h₄
    -- Consider cases m = 1 and m ≥ 2 respectively.
    by_cases h₅ : m = 1
    . -- We have α + β = 1, so n = αβ < 1, a contradiction.
      have : n < 1 := by
        simp [h₅] at hm'
        rify
        nlinarith
      omega
    . -- It suffices to consider the case m ≥ 2.
      replace h₅ : m ≥ 2 := by
        omega
      -- Show that m - 1 < k.
      have h₆ : (m - 1) ^ 2 < k ^ 2 := by
        calc
          (m - 1) ^ 2 ≤ m ^ 2 - 2 := by
            ring_nf
            omega
          _ < (k ^ 2 : ℤ) := h₂
      rw [sq_lt_sq₀ (by omega) (by simp)] at h₆
      -- Show tkat k ≤ m.
      rw [sq_le_sq₀ (by simp) (le_of_lt hm)] at h₃
      -- Show that k = m.
      replace h₃ : k = m := by
        linarith
      clear h₆
      -- We have ⌊mα⌋ + ⌊mβ⌋ = m².
      have h₆ : ⌊m * α⌋ + ⌊m * β⌋ = m ^ 2 := by
        rify
        rw [h₁, <-h₃]
        simp
      -- Show that ⌊α²⌋ + ⌊β²⌋ = α² + β².
      have h₇ : ⌊α ^ 2⌋ + ⌊β ^ 2⌋ = α ^ 2 + β ^ 2 := by
        -- It suffices to show that ⌊α² + n⌋ + ⌊β² + n⌋ = α² + β² + 2n.
        suffices ⌊α ^ 2 + n⌋ + ⌊β ^ 2 + n⌋ = α ^ 2 + β ^ 2 + 2 * n by
          iterate 2 rw [Int.floor_add_int] at this
          push_cast at this
          linarith only [this]
        -- Use the fact that n = αβ and m = α + β.
        calc
          (⌊α ^ 2 + n⌋ + ⌊β ^ 2 + n⌋ : ℝ) = ⌊m * α⌋ + ⌊m * β⌋ := by
            congrm ⌊?_⌋ + ⌊?_⌋
            all_goals
              simp [hm', hn']
              ring
          _ = α ^ 2 + β ^ 2 + 2 * n := by
            rify at h₆
            rw [h₆]
            simp [hm', hn']
            ring
      -- Show that ⌊α²⌋ = α² and ⌊β²⌋ = β².
      have h₈ : ⌊α ^ 2⌋ = α ^ 2 ∧ ⌊β ^ 2⌋ = β ^ 2 := by
        refine ⟨?_, ?_⟩
        <;> linarith only [h₇, Int.floor_le (α ^ 2), Int.floor_le (β ^ 2)]
      -- Now α², β² are both integers.
      replace h₈ : α ^ 2 ∈ Set.range Int.cast ∧ β ^ 2 ∈ Set.range Int.cast := ⟨by aesop, by aesop⟩
      simp at h₈
      obtain ⟨⟨a', h₈⟩, ⟨b', h₉⟩⟩ := h₈
      -- Show that α - β is rational.
      have h₁₀ : α - β ∈ Set.range Rat.cast := by
        -- Note that α - β = (α² - β²) / m.
        use (a' - b') / (m : ℚ)
        rify
        simp [h₈, h₉, hm']
        rw [div_eq_iff (by positivity)]
        ring
      obtain ⟨r, h₁₀⟩ := h₁₀
      -- Show that α, β are rationals.
      have h₁₁ : ∃ (α' β' : ℚ), α = α' ∧ β = β' := by
        use (r + m) / 2, (m - r) / 2
        rify
        rw [h₁₀, hm']
        ring_nf
        tauto
      obtain ⟨α', β', h₁₁⟩ := h₁₁
      -- Now since α², β² are squares and at the same time rational, we have α, β are integers.
      have h₁₂ : IsSquare a' ∧ IsSquare b' := by
        refine ⟨?_, ?_⟩
        . rw [<-Rat.isSquare_intCast_iff]
          -- Note that a' = α² = α'².
          suffices IsSquare (α' * α') by
            convert this using 1
            rify
            rw [h₈, h₁₁.1, pow_two]
          use α'
        . rw [<-Rat.isSquare_intCast_iff]
          -- Note that b' = β² = β'².
          suffices IsSquare (β' * β') by
            convert this using 1
            rify
            rw [h₉, h₁₁.2, pow_two]
          use β'
      -- Now the goal is clear.
      obtain ⟨⟨a, h₁₂⟩, ⟨b, h₁₃⟩⟩ := h₁₂
      rify at h₁₂ h₁₃
      rw [h₈, <-pow_two, <-sq_abs (a : ℝ), sq_eq_sq₀ (le_of_lt h₄α) (by simp)] at h₁₂
      rw [h₉, <-pow_two, <-sq_abs (b : ℝ), sq_eq_sq₀ (le_of_lt h₄β) (by simp)] at h₁₃
      norm_cast at h₁₂ h₁₃
      use |a|, |b|
