import Mathlib

/-Compute the smallest positive integer $n$ for which

$$
0<\sqrt[4]{n}-\lfloor\sqrt[4]{n}\rfloor<\frac{1}{2015}
$$-/

noncomputable def aa (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((1 : ℝ) / 4)⌋₊

noncomputable def bb (n : ℕ) : ℕ := n - (aa n) ^ 4

lemma lemma_1 : ⌊(4097 : ℝ) ^ (4 : ℝ)⁻¹⌋ = 8 := by
  have h1 : (8 : ℝ) ≤ (4097 : ℝ) ^ (4 : ℝ)⁻¹ := by
    have h9 : (8 : ℝ) = ((8 : ℝ) ^ (4 : ℝ)) ^ (4 : ℝ)⁻¹ := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h10 : ((8 : ℝ) ^ (4 : ℝ)) ^ (4 : ℝ)⁻¹ ≤ (4097 : ℝ) ^ (4 : ℝ)⁻¹ := by
      have h5 : (8 : ℝ) ^ (4 : ℝ) ≤ (4097 : ℝ) := by norm_num
      have h6 : (8 : ℝ) ^ (4 : ℝ) ≥ 0 := by positivity
      have h7 : (4097 : ℝ) ≥ 0 := by positivity
      apply Real.rpow_le_rpow
      · linarith
      · linarith
      · norm_num
    linarith [h9, h10]

  have h2 : (4097 : ℝ) ^ (4 : ℝ)⁻¹ < (9 : ℝ) := by
    have h8 : (4097 : ℝ) < (9 : ℝ) ^ (4 : ℝ) := by norm_num
    have h9 : (4097 : ℝ) ^ (4 : ℝ)⁻¹ < ((9 : ℝ) ^ (4 : ℝ)) ^ (4 : ℝ)⁻¹ := by
      have h6 : (4097 : ℝ) ≥ 0 := by positivity
      have h7 : (9 : ℝ) ^ (4 : ℝ) ≥ 0 := by positivity
      apply Real.rpow_lt_rpow
      · linarith
      · nlinarith
      · norm_num
    have h10 : ((9 : ℝ) ^ (4 : ℝ)) ^ (4 : ℝ)⁻¹ = (9 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    nlinarith [h9, h10]

  have h3 : 8 ≤ (4097 : ℝ) ^ (4 : ℝ)⁻¹ := by linarith [h1]
  have h4 : (4097 : ℝ) ^ (4 : ℝ)⁻¹ < (9 : ℝ) := by linarith [h2]

  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try nlinarith

lemma lemma_2 : 8 < (4097 : ℝ) ^ (1 / 4 : ℝ) := by
  have h1 : (8 : ℝ) ^ 4 < (4097 : ℝ) := by norm_num
  have h2 : (8 : ℝ) = ((8 : ℝ) ^ 4) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h3 : ((8 : ℝ) ^ 4) ^ (1 / 4 : ℝ) < (4097 : ℝ) ^ (1 / 4 : ℝ) := by
    apply Real.rpow_lt_rpow
    · -- Show 0 ≤ (8 ^ 4 : ℝ)
      norm_num
    · -- Show (8 ^ 4 : ℝ) < (4097 : ℝ)
      linarith [h1]
    · -- Show (1 / 4 : ℝ) > 0
      norm_num
  linarith [h2, h3]

lemma lemma_3 : (4097 : ℝ) ^ (1 / 4 : ℝ) - 8 < 1 / 2015 := by
  have h1 : (4097 : ℝ) ^ (1 / 4 : ℝ) ≤ (8 + 1 / 2048 : ℝ) := by
    have h2 : (4097 : ℝ) ≤ (8 + 1 / 2048 : ℝ) ^ 4 := by norm_num
    have h3 : (4097 : ℝ) ^ (1 / 4 : ℝ) ≤ ((8 + 1 / 2048 : ℝ) ^ 4) ^ (1 / 4 : ℝ) := by
      apply Real.rpow_le_rpow
      · -- Show 0 ≤ (4097 : ℝ)
        norm_num
      · -- Show (4097 : ℝ) ≤ (8 + 1 / 2048 : ℝ) ^ 4
        linarith [h2]
      all_goals
        norm_num
    have h4 : ((8 + 1 / 2048 : ℝ) ^ 4) ^ (1 / 4 : ℝ) = (8 + 1 / 2048 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        positivity
    rw [h4] at h3
    linarith
  have h2 : (4097 : ℝ) ^ (1 / 4 : ℝ) - 8 ≤ (1 / 2048 : ℝ) := by
    nlinarith [h1]
  have h3 : (1 / 2048 : ℝ) < (1 / 2015 : ℝ) := by norm_num
  linarith [h2, h3]

lemma lemma_4 {a b : Real} (h1 : b < a) (h2 : b ≥ 1) : 1 < a := by 
  linarith

lemma lemma_5 (n : ℕ) : ⌊(n : ℝ) ^ (4 : ℝ)⁻¹⌋ = ↑⌊(n : ℝ) ^ (4 : ℝ)⁻¹⌋₊ := by
  let a := (n : ℝ) ^ (4 : ℝ)⁻¹
  rw [←(show a = (n : ℝ) ^ (4 : ℝ)⁻¹ by rfl)]
  have h1 : a ≥ 0 := by
    unfold a
    positivity
  apply Int.floor_eq_iff.2
  simp
  constructor
  . exact Nat.floor_le h1
  . exact Nat.lt_floor_add_one a

lemma lemma_6 (n : ℕ) (h1 : 0 < (n : ℝ) ^ (1 / 4 : ℝ) - ↑⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋) : ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ ^ 4 < n := by
  rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by simp] at h1
  rw [lemma_5 n] at h1
  simp at h1
  have h2 : (⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℝ) < (n : ℝ) ^ (1 / 4 : ℝ) := by
    simpa using h1
  have h3 : ((⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℝ) ) ^ 4 < (n : ℝ) := by
    have h4 : (⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℝ) < (n : ℝ) ^ (1 / 4 : ℝ) := h2
    have h5 : ((⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℝ) ) ^ 4 < (( (n : ℝ) ^ (1 / 4 : ℝ) ) : ℝ) ^ 4 := by
      apply pow_lt_pow_left₀
      all_goals nlinarith [h4, show (0 : ℝ) ≤ (⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℝ) by positivity]
    have h6 : (( (n : ℝ) ^ (1 / 4 : ℝ) ) : ℝ) ^ 4 = (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    nlinarith
  have h7 : ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ ^ 4 < n := by
    exact_mod_cast h3
  exact h7

theorem number_theory_609463 : IsLeast {n : ℕ | 0 < n ∧ 0 < (n : ℝ) ^ ((1 : ℝ) / 4) - ⌊(n : ℝ) ^ ((1 : ℝ) / 4)⌋ ∧ (n : ℝ) ^ ((1 : ℝ) / 4) - ⌊(n : ℝ) ^ ((1 : ℝ) / 4)⌋ < 1 / 2015} 4097 := by
  constructor
  . -- 4097 ∈ {n | 0 < n ∧ ↑n ^ (1 / 4) - ↑⌊↑n ^ (1 / 4)⌋ < 1 / 2015}
    simp
    unfold Int.fract
    rw [lemma_1]
    norm_num
    constructor
    . exact lemma_2
    . exact lemma_3
  . -- 4097 ∈ lowerBounds {n | 0 < n ∧ ↑n ^ (1 / 4) - ↑⌊↑n ^ (1 / 4)⌋ < 1 / 2015}
    intro n
    simp; norm_num
    intro hn h1 h2
    let a := aa n
    let b := bb n
    have h3 : a ^ 4 < n := by
      unfold Int.fract at h1
      unfold a aa
      exact lemma_6 n h1
    have h4 : n = a ^ 4 + b := by
      unfold a b bb
      rw [←(show a = aa n by unfold a; rfl)]
      omega
    have h5 : b > 0 := by
      unfold b bb
      unfold a at h3
      omega
    have h6 : b < 4 * a ^ 3 + 6 * a ^ 2 + 4 * a + 1 := by
      unfold a b bb
      have : n < (aa n + 1) ^ 4 := by
        unfold aa
        have h1 : (n : ℝ) ≥ 0 := by positivity
        have h3 : ( (n : ℝ) ^ (1 / 4 : ℝ) ) < (⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ + 1 : ℝ) := by
          exact Nat.lt_floor_add_one ( (n : ℝ) ^ (1 / 4 : ℝ) )
        have h6 : ( (n : ℝ) ^ (1 / 4 : ℝ) ) ^ 4 = (n : ℝ) := by
          have h7 : ( (n : ℝ) ^ (1 / 4 : ℝ) ) ^ 4 = (n : ℝ) ^ (1 / 4 * (4 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            ring_nf
            all_goals positivity
          rw [h7]
          norm_num
        have h9 : ( (n : ℝ) ^ (1 / 4 : ℝ) ) ^ 4 < ( (⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ + 1 : ℝ) ) ^ 4 := by
          have h8 : ( (n : ℝ) ^ (1 / 4 : ℝ) ) < (⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ + 1 : ℝ) := h3
          have h10 : ( (n : ℝ) ^ (1 / 4 : ℝ) ) ≥ 0 := by positivity
          have h11 : ( ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ + 1 : ℝ ) ≥ 0 := by
            have h12 : ( ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℝ ) ≥ 0 := by positivity
            nlinarith
          apply pow_lt_pow_left₀
          all_goals nlinarith
        have h10 : (n : ℝ) < (⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ + 1 : ℝ) ^ 4 := by
          have h11 : ( (n : ℝ) ^ (1 / 4 : ℝ) ) ^ 4 = (n : ℝ) := h6
          nlinarith
        exact_mod_cast h10
      ring_nf at this
      omega
    have h7 : a ^ 4 + b < (a + 1 / 2015 : ℝ) ^ 4 := by
      unfold Int.fract at h2
      nth_rw 1 [h4] at h2
      rw [show ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋ = a by unfold a aa; simp; exact lemma_5 n] at h2
      rw [show (((a : ℕ) : ℤ) : ℝ) = ((a : ℕ) : ℝ) by simp] at h2
      have hh1 : ((a ^ 4 + b : ℕ) : ℝ) ^ (1 / 4 : ℝ) < a + 1 / 2015 := by
        linarith
      have h2 : (a ^ 4 + b : ℝ) ≥ 0 := by
        have h3 : (a : ℝ) ^ 4 ≥ 0 := by positivity
        have h4 : (b : ℝ) ≥ 0 := by exact_mod_cast show (b : ℕ) ≥ 0 by omega
        linarith
      have h3 : (a + 1 / 2015 : ℝ) > 0 := by
        have h4 : (a : ℝ) ≥ 0 := by exact_mod_cast show (a : ℕ) ≥ 0 by omega
        norm_num
        all_goals linarith
      have h4 : (a ^ 4 + b : ℝ) < (a + 1 / 2015 : ℝ) ^ 4 := by
        have h5 : ((a ^ 4 + b : ℝ) : ℝ) ^ (1 / 4 : ℝ) < (a + 1 / 2015 : ℝ) := by
          simpa using hh1
        have h7 : (( (a ^ 4 + b : ℝ) : ℝ ) ^ (1 / 4 : ℝ)) ^ 4 < (a + 1 / 2015 : ℝ) ^ 4 := by
          have h8 : ((a ^ 4 + b : ℝ) : ℝ) ^ (1 / 4 : ℝ) < (a + 1 / 2015 : ℝ) := h5
          have h9 : ((a ^ 4 + b : ℝ) : ℝ) ^ (1 / 4 : ℝ) ≥ 0 := by positivity
          have h10 : (a + 1 / 2015 : ℝ) > 0 := h3
          apply pow_lt_pow_left₀
          all_goals nlinarith
        have h7' : (( (a ^ 4 + b : ℝ) : ℝ ) ^ (1 / 4 : ℝ)) ^ 4 = (a ^ 4 + b : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals
          have h8 : (a ^ 4 + b : ℝ) ≥ 0 := h2
          all_goals linarith
        nlinarith
      have h13 : (a : Real) ^ 4 + (b : Real) = (a ^ 4 + b : ℝ) := by
        ring_nf
      have h14 : ((a : Real) + 1 / 2015) ^ 4 = (a + 1 / 2015 : ℝ) ^ 4 := by
        ring_nf
      rw [h13, h14]
      linarith
    have h8 : b ≥ 1 := by linarith
    have h9 : a ≥ 8 := by
      ring_nf at h7
      have hh1 : (b : ℝ) < 1 / 16485427050625 + ↑a * (4 / 8181353375) + ↑a ^ 2 * (6 / 4060225) + ↑a ^ 3 * (4 / 2015) := by
        linarith
      have hh2 := lemma_4 hh1 (by simp; exact h8)
      by_contra h
      push_neg at h
      have h1 : a ≤ 7 := by omega
      interval_cases a <;> norm_num at hh2 ⊢
    rw [h4]
    have h10 : a ^ 4 ≥ 4096 := by
      have h1 : a ≥ 8 := h9
      have h2 : a ^ 4 ≥ (8 : ℕ) ^ 4 := by
        apply Nat.pow_le_pow_left
        all_goals omega
      norm_num at h2 ⊢
      all_goals omega
    linarith

