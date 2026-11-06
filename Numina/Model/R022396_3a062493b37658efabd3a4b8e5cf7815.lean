import Mathlib

theorem algebra_3990 :
    IsGreatest {b : ℝ | ∃ f : ℝ → ℝ, (∀ x, f x + f (-x) = x ^ 2 + (b ^ 2 - 5 * b + 6) * x + 1)} 3 := by
  constructor
  · -- First, show that 3 is in the set
    use fun x =>
      if x = 0 then (1 / 2 : ℝ)
      else ((x ^ 2) / 2 + 1 / 2)
    intro x
    by_cases h : x = 0
    · -- Case where x = 0
      rw [h]
      norm_num
    · -- Case where x ≠ 0
      have hx1 : x ≠ 0 := by
        intro hx0
        apply h
        linarith
      simp [hx1, show x ≠ 0 by assumption]
      <;> ring_nf
      <;> norm_num [hx1]
  · -- Now show that 3 is greatest in the set
    intro b hb
    rcases hb with ⟨f, hf⟩
    have eq1 := hf 1
    have eq2 := hf (-1 : ℝ)
    have h0 := hf 0
    norm_num at h0 eq1 eq2
    have h1 : (b - 2) * (b - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case where b - 2 = 0, so b = 2
      nlinarith
    · -- Case where b - 3 = 0, so b = 3
      linarith