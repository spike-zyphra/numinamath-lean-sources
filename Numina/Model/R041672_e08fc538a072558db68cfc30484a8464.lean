import Mathlib

theorem algebra_165412 {n : ℕ} (hn : n > 0) (a b : ℝ)
    (ha : a = 20) (hb : b = 4) (r s : ℚ)
    (hr : r = 3 / 4) (hs : s = 2 / 3)
    (h : ∑ i ∈ Finset.range n, a * r ^ i * b * s ^ i = 158.75) :
    n = 7 := by
  rw [ha, hb, hr, hs] at h
  have h1 : ∑ i in Finset.range n, (20 : ℝ) * ((3 / 4 : ℚ) : ℝ) ^ i * (4 : ℝ) * ((2 / 3 : ℚ) : ℝ) ^ i = 158.75 := h
  have h2 : ∑ i in Finset.range n, (20 : ℝ) * ((3 / 4 : ℚ) : ℝ) ^ i * (4 : ℝ) * ((2 / 3 : ℚ) : ℝ) ^ i =
      160 * (1 - ((1:ℝ)/2)^n) := by
    have h3 : ∀ i : ℕ, (20 : ℝ) * ((3 / 4 : ℚ) : ℝ) ^ i * (4 : ℝ) * ((2 / 3 : ℚ) : ℝ) ^ i = 80 * ((1 : ℝ) / 2) ^ i := by
      intro i
      have eq1 : (20 : ℝ) * ((3 / 4 : ℚ) : ℝ) ^ i * (4 : ℝ) * ((2 / 3 : ℚ) : ℝ) ^ i = 80 * ( ( (3 / 4 : ℚ) : ℝ ) * ( (2 / 3 : ℚ) : ℝ ) ) ^ i := by
        have eq2 : (20 : ℝ) * ((3 / 4 : ℚ) : ℝ) ^ i * (4 : ℝ) * ((2 / 3 : ℚ) : ℝ) ^ i =
              (20 * (4 : ℝ)) * ( ( (3 / 4 : ℚ) : ℝ ) ^ i * ( ( (2 / 3 : ℚ) : ℝ ) ^ i ) ) := by ring
        have eq3 : (20 * (4 : ℝ)) = (80 : ℝ) := by norm_num
        have eq4 : ( ( (3 / 4 : ℚ) : ℝ ) ^ i * ( ( (2 / 3 : ℚ) : ℝ ) ^ i ) ) = ( ( ( (3 / 4 : ℚ) : ℝ ) * ( (2 / 3 : ℚ) : ℝ ) ) ) ^ i := by
          have h11 : ∀ i : ℕ, ( ( (3 / 4 : ℚ) : ℝ ) ^ i * ( (2 / 3 : ℚ) : ℝ ) ^ i ) = ( ( ( (3 / 4 : ℚ) : ℝ ) * ( (2 / 3 : ℚ) : ℝ ) ) ) ^ i := by
            intro i
            induction i with
            | zero =>
              simp
            | succ n ih =>
              simp [pow_succ, mul_add, mul_pow] at ih ⊢
              <;> nlinarith
          specialize h11 i
          simpa using h11
        rw [eq2, eq3, eq4]
      have eq5 : ( ( (3 / 4 : ℚ) : ℝ ) * ( (2 / 3 : ℚ) : ℝ ) ) = ( (1 / 2 : ℝ ) ) := by
        norm_num
      have eq6 : 80 * ( ( ( (3 / 4 : ℚ) : ℝ ) * ( (2 / 3 : ℚ) : ℝ ) ) ) ^ i = 80 * ( (1 / 2 : ℝ ) ) ^ i := by
        rw [eq5]
      linarith [eq1, eq6]
    rw [Finset.sum_congr rfl (fun i _ => h3 i)]
    have h4 : ∑ i in Finset.range n, 80 * ((1 : ℝ) / 2) ^ i = 160 * (1 - ((1 : ℝ) / 2) ^ n) := by
      have h5 : ∀ (k : ℕ), ∑ i in Finset.range k, 80 * ((1: ℝ) / 2) ^ i =
          160 * (1 - ((1: ℝ) / 2) ^ k) := by
        intro k
        induction k with
        | zero =>
          simp
          <;> norm_num
        | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          field_simp at *
          ring
      specialize h5 n
      simpa using h5
    rw [h4]
  rw [h2] at h1
  have h4 : (1 - ((1:ℝ)/2) ^ n) = (158.75 / (160 : ℝ)) := by
    norm_num at h1 ⊢
    linarith
  have h5 : ((1:ℝ)/2) ^ n = (1 : ℝ) / 128 := by
    have h6 : ((1:ℝ)/2) ^ n = 1 - (158.75 / (160 : ℝ)) := by linarith [h4]
    rw [h6]
    norm_num
  have h6 : ((1 : ℝ) / 2) ^ n = ((1 : ℝ) / 2) ^ 7 := by
    rw [h5]
    norm_num
  have h7 : n = 7 := by
    have h8 : ( (1 : ℝ) / 2 ) ^ n = ( (1 : ℝ) / 2 ) ^ 7 := h6
    exact Nat.cast_injective ((by simpa using h8))
  exact h7