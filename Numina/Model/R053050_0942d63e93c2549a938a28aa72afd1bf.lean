import Mathlib

theorem algebra_92087 {f : Polynomial ℤ} (hf1 : f.eval 1 = -1) (hf2 : f.eval 4 = 2)
    (hf3 : f.eval 8 = 34) (n : ℤ) (hn : f.eval n = n ^ 2 - 4 * n - 18) :
    n = 6 ∨ n = 3 := by

  have h1 : (n - 1) ∣ (n^2 - 4 * n - 17) := by
    have h1 : (n - 1) ∣ (f.eval n - f.eval 1) := by
      apply Polynomial.sub_dvd_eval_sub
    have h2 : f.eval n - f.eval 1 = (n^2 - 4 * n - 17) := by
      rw [hn, hf1]
      ring
    rw [h2] at h1
    exact h1

  have h2 : (n - 4) ∣ (n^2 - 4 * n - 20) := by
    have h3 : (n - 4) ∣ (f.eval n - f.eval 4) := by
      apply Polynomial.sub_dvd_eval_sub
    have h4 : f.eval n - f.eval 4 = (n^2 - 4 * n - 20) := by
      rw [hn, hf2]
      ring
    rw [h4] at h3
    exact h3

  have h3 : (n - 8) ∣ (n^2 - 4 * n - 52) := by
    have h4 : (n - 8) ∣ (f.eval n - f.eval 8) := by
      apply Polynomial.sub_dvd_eval_sub
    have h5 : f.eval n - f.eval 8 = (n^2 - 4 * n - 52) := by
      rw [hn, hf3]
      ring
    rw [h5] at h4
    exact h4

  have h4 : (n - 1) ∣ 20 := by
    obtain ⟨k, hk⟩ := h1
    have eq1 : n^2 - 4 * n - 17 = (n - 1) * k := by linarith [hk]
    have eq2 : (n - 1) * k + 20 = (n - 1) * (n - 3) := by
      nlinarith
    use (n - 3 - k)
    nlinarith

  have h5 : (n - 4) ∣ 20 := by
    obtain ⟨k, hk⟩ := h2
    have eq1 : n^2 - 4 * n - 20 = (n - 4) * k := by linarith [hk]
    have eq2 : (n - 4) * k + 20 = (n - 4) * (n) := by
      nlinarith
    use (n - k)
    nlinarith

  have h6 : (n - 8) ∣ 20 := by
    obtain ⟨k, hk⟩ := h3
    have eq1 : n^2 - 4 * n - 52 = (n - 8) * k := by linarith [hk]
    have eq2 : (n - 8) * k + 20 = (n - 8) * (n + 4) := by
      nlinarith
    use (n + 4 - k)
    nlinarith

  have h5 : n ≤ 28 := by
    have h11 : (n - 8) ∣ 20 := h6
    have h12 : (n - 8) ≤ 20 := by 
      apply Int.le_of_dvd (by norm_num) h11
    omega

  have h6 : n ≥ -12 := by
    have h11 : (n - 8) ∣ 20 := h6
    have h13 : (n - 8) ≥ -20 := by
      have h14 : -(n - 8) ∣ 20 := by 
        exact Int.neg_dvd.2 h11
      have h15 : -(n - 8) ≤ 20 := by
        apply Int.le_of_dvd (by norm_num) h14
      linarith
    omega

  interval_cases n <;> norm_num at hn ⊢ <;> tauto