import Mathlib

theorem algebra_505517 {f : ℝ → ℝ} {m : ℤ}
    (hf : ∀ x : ℝ, f x = x ^ (m ^ 2 - 4 * m))
    (h_symm : ∀ x, f x = f (-x))
    (h_desc : ∀ x > 0, deriv f x < 0) :
    m = 2 := by

  have l_even_of_zpow_symm (a : ℤ) (h : ∀ x : ℝ, x ^ a = (-x) ^ a) : Even a := by
    by_contra!
    apply Int.not_even_iff_odd.mp at this
    specialize h 1
    norm_num [one_zpow, Odd.neg_one_zpow this] at h


  have p1 : Even (m ^ 2 - 4 * m) := by
    simp_rw [hf] at h_symm
    exact l_even_of_zpow_symm _ h_symm

  have p2 : m ^ 2 - 4 * m < 0 := by
    have fderiv : f = fun x => x ^ (m ^ 2 - 4 * m) := by
      funext x
      exact hf x
    have := h_desc 1 (by norm_num)
    simp [fderiv, deriv_zpow'] at this
    -- `this` should be `(m : ℝ) ^ 2 < 4 * (m : ℝ)` here
    rify
    exact sub_neg.mpr this

  have : 0 < m ∧ m < 4 := by
    rw [show m ^ 2 - 4 * m = m * (m - 4) by ring] at p2
    rcases mul_neg_iff.mp p2 with h | h
    all_goals omega

  obtain ⟨hmgt, hmle⟩ := this
  interval_cases m
  any_goals norm_num [even_iff_two_dvd] at p1 ⊢
