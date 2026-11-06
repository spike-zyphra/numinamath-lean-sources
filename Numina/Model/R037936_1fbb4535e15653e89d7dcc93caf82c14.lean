import Mathlib

theorem algebra_217988 {a b : ℝ} (h₀ : a^2 + b^2 = a^2 * b^2) (h₁ : abs a ≠ 1) (h₂ : abs b ≠ 1) :
    a^7 / (1 - a)^2 - a^7 / (1 + a)^2 = b^7 / (1 - b)^2 - b^7 / (1 + b)^2 := by

  have ha1 : a - 1 ≠ 0 := by
    intro h
    have h3 : a = 1 := by linarith
    have h4 : abs a = 1 := by
      rw [h3]
      norm_num
    contradiction

  have ha2 : a + 1 ≠ 0 := by
    intro h
    have h3 : a = -1 := by linarith
    have h4 : abs a = 1 := by
      rw [h3]
      norm_num
    contradiction

  have hb1 : b - 1 ≠ 0 := by
    intro h
    have h3 : b = 1 := by linarith
    have h4 : abs b = 1 := by
      rw [h3]
      norm_num
    contradiction

  have hb2 : b + 1 ≠ 0 := by
    intro h
    have h3 : b = -1 := by linarith
    have h4 : abs b = 1 := by
      rw [h3]
      norm_num
    contradiction

  have h3 : 1 - a ≠ 0 := by
    intro h
    apply ha1
    linarith

  have h4 : 1 + a ≠ 0 := by
    intro h
    apply ha2
    linarith

  have h5 : 1 - b ≠ 0 := by
    intro h
    apply hb1
    linarith

  have h6 : 1 + b ≠ 0 := by
    intro h
    apply hb2
    linarith

  have eq1 : a^7 / (1 - a) ^ 2 - a^7 / (1 + a) ^ 2 =
    (a^7 * ((1 + a)^2 - (1 - a)^2)) / ((1 - a) ^ 2 * (1 + a) ^ 2) := by
    field_simp [(show 1 - a ≠ 0 by exact h3), (show 1 + a ≠ 0 by exact h4)]
    <;> ring

  have eq2 : b^7 / (1 - b) ^ 2 - b^7 / (1 + b) ^ 2 =
    (b^7 * ((1 + b)^2 - (1 - b)^2)) / ((1 - b) ^ 2 * (1 + b) ^ 2) := by
    field_simp [(show 1 - b ≠ 0 by exact h5), (show 1 + b ≠ 0 by exact h6)]
    <;> ring

  rw [eq1, eq2]

  have eq3 : a^7 * ((1 + a)^2 - (1 - a)^2) = 4 * a^8 := by
    ring_nf

  have eq4 : b^7 * ((1 + b)^2 - (1 - b)^2) = 4 * b^8 := by
    ring_nf

  rw [eq3, eq4]

  have eq5 : (1 - a) ^ 2 * (1 + a) ^ 2 = (1 - a^2)^2 := by
    ring_nf

  have eq6 : (1 - b) ^ 2 * (1 + b) ^ 2 = (1 - b^2)^2 := by
    ring_nf

  rw [eq5, eq6]

  have eq7 : (1 - a^2) * (1 - b^2) = 1 := by
    nlinarith

  have h8 : (1 - a^2)^2 * (1 - b^2)^2 = 1 := by
    calc
      (1 - a^2)^2 * (1 - b^2)^2 = ((1 - a^2) * (1 - b^2)) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [eq7]
      _ = 1 := by norm_num

  field_simp [(show 1 - a^2 ≠ 0 by
    by_contra h
    have h7 : a^2 = 1 := by nlinarith
    have h71 : abs a = 1 := by
      rw [abs_eq]
      all_goals nlinarith
    contradiction
  ), (show 1 - b^2 ≠ 0 by
    by_contra h
    have h7 : b^2 = 1 := by nlinarith
    have h71 : abs b = 1 := by
      rw [abs_eq]
      all_goals nlinarith
    contradiction
  ), h8]
  <;> nlinarith [sq_pos_of_pos (show 0 < (2 : ℝ) by norm_num), sq_nonneg (a^2 - b^2), sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 -1), sq_nonneg (b^2 -1)]