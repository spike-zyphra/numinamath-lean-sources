import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_141974 {f : ℝ → ℝ} (hf : f = λ x => sqrt (1 - (cos (2 * x))^2)) :
    ∀ x, f x = 0 ↔ ∃ k : ℤ, x = k * π / 2 := by
  intro x
  constructor
  · -- Forward: If $f(x) = 0$, then $x = \frac{k\pi}{2}$ for some integer $k$.
    intro hfx
    have hfx' : sqrt (1 - (cos (2 * x))^2) = 0 := by
      rw [hf] at hfx 
      exact hfx 
    have h1 : 1 - (cos (2 * x))^2 = 0 := by
      calc
        1 - (cos (2 * x))^2 = (sqrt (1 - (cos (2 * x))^2)) ^ 2 := by 
          rw [Real.sq_sqrt]
          nlinarith [Real.sin_sq_add_cos_sq (2 * x)]
        _ = 0 ^ 2 := by 
          rw [hfx']
        _ = 0 := by 
          norm_num 
    have h2 : sin (2 * x) ^ 2 = 0 := by 
      have hsin : sin (2 * x) ^ 2 = 1 - cos (2 * x) ^ 2 := by 
        have h : sin (2 * x) ^ 2 + cos (2 * x) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * x)
        linarith 
      rw [hsin] 
      nlinarith 
    have h3 : sin (2 * x) = 0 := by 
      nlinarith 
    obtain ⟨k, hk⟩ := sin_eq_zero_iff.1 h3 
    use k 
    have hk' : 2 * x = (k : ℝ) * π := by 
      linarith [hk] 
    field_simp at hk' ⊢ 
    <;> nlinarith 
  · -- Backward: If $x = \frac{k\pi}{2}$ for some integer $k$, then $f(x) = 0$.
    rintro ⟨k, hk⟩
    rw [hf]
    have hk2 : 2 * x = (k : ℝ) * π := by 
      have h1 : x = (k : ℝ) * π / 2 := by linarith [hk]
      linarith [h1]
    have hk3 : cos (2 * x) = cos (k * π) := by 
      rw [show 2 * x = k * π by linarith [hk2]]
    have hk4 : cos (k * π) ^ 2 = 1 := by 
      have hsin : sin (k * π) = 0 := by 
        have hk2 : sin (k * π) = 0 := by 
          have : sin ((k : ℝ) * π) = 0 := by 
            exact sin_int_mul_pi k 
          exact_mod_cast this 
        exact_mod_cast hk2 
      have h12 : cos (k * π) ^ 2 = 1 := by 
        have hcos : cos (k * π) ^ 2 + sin (k * π) ^ 2 = 1 := by 
          exact Real.cos_sq_add_sin_sq (k * π) 
        rw [hsin] at hcos 
        nlinarith 
      exact_mod_cast h12 
    simp only [hk3]
    rw [hk4] 
    rw [sub_self] 
    simp 
    all_goals norm_num [Real.sq_sqrt] 
    <;> nlinarith 
    all_goals try { tauto }
    all_goals try { try { tauto } }
    all_goals try { try { tauto } }
    all_goals try { tauto }
    all_goals norm_cast at *
    <;> norm_num 
    <;> try { tauto } 
    <;> nlinarith 
    all_goals try { tauto }