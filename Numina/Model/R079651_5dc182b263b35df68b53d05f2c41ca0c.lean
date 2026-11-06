import Mathlib

open Real Set
open scoped Real

theorem algebra_318949 (f : ℝ → ℝ) (hf : f = λ x => (2 - cos x) / sin x) :
    IsLeast {y | ∃ x, 0 < x ∧ x < Real.pi ∧ f x = y} (Real.sqrt 3) := by
  constructor
  · -- Show that sqrt 3 is in the set
    use Real.pi / 3
    constructor
    · -- Show that 0 < π/3
      linarith [Real.pi_pos]
    constructor
    · -- Show that π/3 < π
      linarith [Real.pi_pos]
    · -- Show that f (π/3) = sqrt 3
      rw [hf]
      have hcos : cos (Real.pi / 3) = 1 / 2 := by
        exact Real.cos_pi_div_three
      have hsin : sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
        exact Real.sin_pi_div_three
      simp [hcos, hsin]
      <;> field_simp [Real.sqrt_pos.mpr]
      <;> ring_nf <;> norm_num [Real.sq_sqrt]
  · -- Show that sqrt 3 is the smallest
    intro y
    intro hy
    rcases hy with ⟨x, hx1, hx2, hfy⟩
    rw [hf] at hfy
    have h1 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      exact hx1
      exact hx2
    have h2 : (2 - cos x) / sin x = y := by
      simpa using hfy
    have h4 : Real.sqrt 3 * sin x + cos x ≤ 2 := by
      nlinarith [sq_nonneg (sin x), sq_nonneg (cos x - 1 / 2), sq_nonneg (sin x - Real.sqrt 3 / 2), sq_nonneg (x - Real.pi / 3),
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3,
        Real.sin_pos_of_pos_of_lt_pi (show 0 < x by linarith) (show x < Real.pi by linarith),
        Real.cos_sq_add_sin_sq x, Real.sin_sq_add_cos_sq x,
        Real.sin_sq_add_cos_sq (x - Real.pi / 3), Real.sin_sq_add_cos_sq (Real.pi / 3),
        Real.cos_pi_div_three, Real.sin_pi_div_three
      ]
    have h5 : Real.sqrt 3 ≤ ( (2 - cos x) / sin x : ℝ ) := by
      have h6 : sin x > 0 := h1
      have h7 : Real.sqrt 3 * sin x ≤ 2 - cos x := by linarith
      have h8 : (2 - cos x) / sin x = y := by
        linarith
      have h9 : (2 - cos x) / sin x = (2 - cos x) / sin x := by rfl
      apply (le_div_iff₀ (by linarith)).mpr
      linarith
    linarith [h2, h5, h1, Real.sqrt_nonneg 3]