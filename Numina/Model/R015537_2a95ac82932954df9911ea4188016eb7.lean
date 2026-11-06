import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_130125 {d : ℕ → ℝ}
  (hd : ∀ k, d k = |(200 : ℝ) - 2.4 * k| + |(300 : ℝ) - 4.2 * k|) :
  IsLeast {x | ∃ k, x = d k} (d 72) := by
  constructor
  · -- Show that $d(72)$ is in the set
    use 72
  · -- Show that $d(72)$ is less than or equal to all other elements in the set
    intro x hx
    rcases hx with ⟨k, hk⟩
    have h1 : d 72 = (29.6 : ℝ) := by
      rw [hd 72]
      norm_num [abs_of_pos, abs_of_nonneg, abs_of_nonpos, mul_add, mul_assoc]
    have h2 : d k = |(200 : ℝ) - 2.4 * (k : ℝ)| + |(300 : ℝ) - 4.2 * (k : ℝ)| := by
      specialize hd k
      simpa using hd
    have hk' : x = |(200 : ℝ) - 2.4 * (k : ℝ)| + |(300 : ℝ) - 4.2 * (k : ℝ)| := by
      linarith [hk, h2]
    rw [hk']
    rw [h1]
    have hk1 : |(200 : ℝ) - 2.4 * (k : ℝ)| + |(300 : ℝ) - 4.2 * (k : ℝ)| ≥ (29.6 : ℝ) := by
      by_cases h1 : (200 : ℝ) - 2.4 * (k : ℝ) ≥ 0
      · -- If $200 - 2.4k \geq 0$, then $|200 - 2.4k| = 200 - 2.4k$
        rw [abs_of_nonneg h1]
        by_cases h2 : (300 : ℝ) - 4.2 * (k : ℝ) ≥ 0
        · -- If $300 - 4.2k \geq 0$, then $|300 - 4.2k| = 300 - 4.2k$
          rw [abs_of_nonneg h2]
          have hk4 : k ≤ 71 := by
            by_contra h
            push_neg at h
            have hk5 : k ≥ 72 := by omega
            have hk6 : (k : ℝ) ≥ (72 : ℝ) := by exact_mod_cast hk5
            nlinarith
          have hk3' : (k : ℝ) ≤ (71 : ℝ) := by
            exact_mod_cast (show k ≤ 71 by omega)
          nlinarith
        · -- If $300 - 4.2k < 0$, then $|300 - 4.2k| = -(300 - 4.2k)$
          rw [abs_of_neg (lt_of_not_ge h2)]
          have hk4 : k ≥ 72 := by
            by_contra h
            push_neg at h
            have hk3 : k < 72 := by linarith
            have hk4 : k ≤ 71 := by omega
            have hk5 : (k : ℝ) ≤ (71 : ℝ) := by exact_mod_cast hk4
            nlinarith
          have hk3' : (k : ℝ) ≥ (72 : ℝ) := by
            exact_mod_cast (show k ≥ 72 by omega)
          nlinarith
      · -- If $200 - 2.4k < 0$, then $|200 - 2.4k| = -(200 - 2.4k)$
        rw [abs_of_neg (lt_of_not_ge h1)]
        by_cases h2 : (300 : ℝ) - 4.2 * (k : ℝ) ≥ 0
        · -- If $300 - 4.2k \geq 0$, then $|300 - 4.2k| = 300 - 4.2k$
          rw [abs_of_nonneg h2]
          have hk3 : k > (83.333 : ℝ) := by
            nlinarith
          have hk4 : k ≤ 39 := by
            by_contra h
            push_neg at h
            have hk5 : k > 39 := by
              omega
            have hk6 : (k : ℝ) > (39 : ℝ) := by
              exact_mod_cast hk5
            nlinarith
          have hk5 : k ≤ 39 := by
            omega
          have hk6 : (k : ℝ) ≤ (39 : ℝ) := by
            exact_mod_cast hk5
          nlinarith
        · -- If $300 - 4.2k < 0$, then $|300 - 4.2k| = -(300 - 4.2k)$
          rw [abs_of_neg (lt_of_not_ge h2)]
          have hk4 : k ≥ 84 := by
            by_contra h
            push_neg at h
            have hk3 : k < 84 := by linarith
            have hk4 : k ≤ 83 := by omega
            have hk5 : (k : ℝ) ≤ (83 : ℝ) := by
              exact_mod_cast hk4
            nlinarith
          have hk3' : (k : ℝ) ≥ (84 : ℝ) := by
            exact_mod_cast (show k ≥ 84 by omega)
          nlinarith
    linarith