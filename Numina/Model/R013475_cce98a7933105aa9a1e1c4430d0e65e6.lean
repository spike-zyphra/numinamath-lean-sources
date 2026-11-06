import Mathlib

theorem algebra_321445 {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : a * b * c * d ≠ 0) :
    a / |a| - b / |b| - c / |c| + d / |d| + a * b / |a * b| + a * c / |a * c| -
    a * d / |a * d| - b * c / |b * c| + b * d / |b * d| + c * d / |c * d| +
    a * b * c / |a * b * c| - a * b * d / |a * b * d| - a * c * d / |a * c * d| +
    b * c * d / |b * c * d| - a * b * c * d / |a * b * c * d| = 1 ∨
    a / |a| - b / |b| - c / |c| + d / |d| + a * b / |a * b| + a * c / |a * c| -
    a * d / |a * d| - b * c / |b * c| + b * d / |b * d| + c * d / |c * d| +
    a * b * c / |a * b * c| - a * b * d / |a * b * d| - a * c * d / |a * c * d| +
    b * c * d / |b * c * d| - a * b * c * d / |a * b * c * d| = -15 := by
  have h5 : a * b / |a * b| = (a / |a|) * (b / |b|) := by
    field_simp [abs_mul]
  have h6 : a * c / |a * c| = (a / |a|) * (c / |c|) := by
    field_simp [abs_mul]
  have h7 : a * d / |a * d| = (a / |a|) * (d / |d|) := by
    field_simp [abs_mul]
  have h8 : b * c / |b * c| = (b / |b|) * (c / |c|) := by
    field_simp [abs_mul]
  have h9 : b * d / |b * d| = (b / |b|) * (d / |d|) := by
    field_simp [abs_mul]
  have h10 : c * d / |c * d| = (c / |c|) * (d / |d|) := by
    field_simp [abs_mul]
  have h11 : a * b * c / |a * b * c| = (a / |a|) * (b / |b|) * (c / |c|) := by
    field_simp [abs_mul]
  have h12 : a * b * d / |a * b * d| = (a / |a|) * (b / |b|) * (d / |d|) := by
    field_simp [abs_mul]
  have h13 : a * c * d / |a * c * d| = (a / |a|) * (c / |c|) * (d / |d|) := by
    field_simp [abs_mul]
  have h14 : b * c * d / |b * c * d| = (b / |b|) * (c / |c|) * (d / |d|) := by
    field_simp [abs_mul]
  have h15 : a * b * c * d / |a * b * c * d| = (a / |a|) * (b / |b|) * (c / |c|) * (d / |d|) := by
    field_simp [abs_mul]
  simp only [h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  have ha1 : a / |a| = 1 ∨ a / |a| = -1 := by
    cases (le_or_lt 0 a) with
    | inl h1 =>
      have : a > 0 := by
        by_contra h
        push_neg at h
        have : a = 0 := by linarith
        contradiction
      have ha1 : a / |a| = 1 := by
        rw [abs_of_pos this]
        field_simp
      simp [ha1]
    | inr h2 =>
      have : a < 0 := by
        by_contra h
        push_neg at h
        have : a = 0 := by linarith
        contradiction
      have ha1 : a / |a| = -1 := by
        rw [abs_of_neg this]
        field_simp
      simp [ha1]
  have hb1 : b / |b| = 1 ∨ b / |b| = -1 := by
    cases (le_or_lt 0 b) with
    | inl h1 =>
      have : b > 0 := by
        by_contra h
        push_neg at h
        have : b = 0 := by linarith
        contradiction
      have hb1 : b / |b| = 1 := by
        rw [abs_of_pos this]
        field_simp
      simp [hb1]
    | inr h2 =>
      have : b < 0 := by
        by_contra h
        push_neg at h
        have : b = 0 := by linarith
        contradiction
      have hb1 : b / |b| = -1 := by
        rw [abs_of_neg this]
        field_simp
      simp [hb1]
  have hc1 : c / |c| = 1 ∨ c / |c| = -1 := by
    cases (le_or_lt 0 c) with
    | inl h1 =>
      have : c > 0 := by
        by_contra h
        push_neg at h
        have : c = 0 := by linarith
        contradiction
      have hc1 : c / |c| = 1 := by
        rw [abs_of_pos this]
        field_simp
      simp [hc1]
    | inr h2 =>
      have : c < 0 := by
        by_contra h
        push_neg at h
        have : c = 0 := by linarith
        contradiction
      have hc1 : c / |c| = -1 := by
        rw [abs_of_neg this]
        field_simp
      simp [hc1]
  have hd1 : d / |d| = 1 ∨ d / |d| = -1 := by
    cases (le_or_lt 0 d) with
    | inl h1 =>
      have : d > 0 := by
        by_contra h
        push_neg at h
        have : d = 0 := by linarith
        contradiction
      have hd1 : d / |d| = 1 := by
        rw [abs_of_pos this]
        field_simp
      simp [hd1]
    | inr h2 =>
      have : d < 0 := by
        by_contra h
        push_neg at h
        have : d = 0 := by linarith
        contradiction
      have hd1 : d / |d| = -1 := by
        rw [abs_of_neg this]
        field_simp
      simp [hd1]
  rcases ha1 with ha1 | ha1 <;> rcases hb1 with hb1 | hb1 <;> rcases hc1 with hc1 | hc1 <;> rcases hd1 with hd1 | hd1
  <;> norm_num [ha1, hb1, hc1, hd1]
  <;> tauto