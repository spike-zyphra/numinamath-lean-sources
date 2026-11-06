import Mathlib

open Real

theorem inequalities_113372 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc 1 2) (hb : ∀ i, b i ∈ Set.Icc 1 2)
    (h : ∑ i, a i ^ 2 = ∑ i, b i ^ 2) :
    ∑ i, a i ^ 3 / b i ≤ (17 / 10) * ∑ i, a i ^ 2 := by

  have h1 : ∀ i, 1 ≤ a i ∧ a i ≤ 2 := by
    intro i
    exact ha i

  have h2 : ∀ i, 1 ≤ b i ∧ b i ≤ 2 := by
    intro i
    exact hb i

  have h3 : ∀ i, a i ^ 3 / b i ≤ (21 / 10) * (a i ^ 2) - (2 / 5) * (b i ^ 2) := by
    intro i
    have ha1 : 1 ≤ a i := (h1 i).1
    have ha2 : a i ≤ 2 := (h1 i).2
    have hb1 : 1 ≤ b i := (h2 i).1
    have hb2 : b i ≤ 2 := (h2 i).2
    have h4 : 0 < b i := by linarith
    have h5 : a i ^ 3 ≤ (21 / 10) * (a i ^ 2) * (b i) - (2 / 5) * (b i ^ 3) := by
      have h6 : 10 * (a i) ^ 3 - 21 * (a i) ^ 2 * (b i) + 4 * (b i) ^ 3 ≤ 0 := by
        have h7 : 10 * (a i) ^ 3 - 21 * (a i) ^ 2 * (b i) + 4 * (b i) ^ 3 =
            (a i - 2 * b i) * (a i - (1/2) * b i) * (10 * a i + 4 * b i) := by
          ring
        rw [h7]
        have h8 : (a i - 2 * b i) ≤ 0 := by
          nlinarith
        have h9 : (a i - (1/2) * b i) ≥ 0 := by
          nlinarith
        have h10 : (10 * a i + 4 * b i) ≥ 0 := by
          nlinarith
        have h11 : (a i - 2 * b i) * (a i - (1/2) * b i) ≤ 0 := by
          nlinarith
        have h12 : (a i - 2 * b i) * (a i - (1/2) * b i) * (10 * a i + 4 * b i) ≤ 0 := by
          have h13 : (a i - 2 * b i) * (a i - (1/2) * b i) ≤ 0 := h11
          have h14 : (10 * a i + 4 * b i) ≥ 0 := h10
          nlinarith
        linarith
      nlinarith
    have h10 : a i ^ 3 / b i ≤ (21 / 10) * (a i ^ 2) - (2 / 5) * (b i ^ 2) := by
      have h11 : a i ^ 3 ≤ (21 / 10) * (a i ^ 2) * (b i) - (2 / 5) * (b i) ^ 3 := h5
      have h12 : 0 < b i := by linarith
      have h13 : a i ^ 3 / b i ≤ ( (21 / 10) * (a i ^ 2) * (b i) - (2 / 5) * (b i) ^ 3 ) / (b i) := by
        apply (div_le_div_right (by linarith)).mpr
        linarith
      have h14 : ( (21 / 10) * (a i ^ 2) * (b i) - (2 / 5) * (b i) ^ 3 ) / (b i) = (21 / 10) * (a i ^ 2) - (2 / 5) * (b i ^ 2) := by
        field_simp
        all_goals
          nlinarith
      linarith [h13, h14]
    linarith

  have h4 : ∑ i, a i ^ 3 / b i ≤ ∑ i, ((21 / 10) * (a i ^ 2) - (2 / 5) * (b i ^ 2)) := by
    apply Finset.sum_le_sum
    intro i _
    specialize h3 i
    linarith

  have h5 : ∑ i, ((21 / 10) * (a i ^ 2) - (2 / 5) * (b i ^ 2)) = (21 / 10) * ∑ i, (a i ^ 2) - (2 / 5) * ∑ i, (b i ^ 2) := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum]

  rw [h5] at h4

  have h6 : (21 / 10) * ∑ i, (a i ^ 2) - (2 / 5) * ∑ i, (b i ^ 2) = (17 / 10) * ∑ i, (a i ^ 2) := by
    have h7 : ∑ i, (a i ^ 2) = ∑ i, (b i ^ 2) := h
    rw [show ∑ i, (b i ^ 2) = ∑ i, (a i ^ 2) by linarith [h7]]
    linarith

  linarith [h6, h4]