import Mathlib

lemma rtt : (∀ (i : ℕ), i < 4 → ∃ n : ℕ, ∃ a : ℕ → ℤ,
    a 0 = 0 ∧
    a n = i ∧
    ∀ j ∈ Finset.Icc 1 n, |a j - a (j - 1)| = (j : ℤ) ^ 2) := by
  intro i h
  have h_main : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    have h₁ : i < 4 := h
    have h₂ : i ≤ 3 := by linarith
    interval_cases i <;> norm_num at h₂ ⊢ <;> omega
  
  rcases h_main with (rfl | rfl | rfl | rfl)
  · -- Case i = 0
    refine' ⟨0, fun j ↦ 0, by simp, by simp, _⟩
    simp [Finset.mem_Icc]
    <;> aesop
  · -- Case i = 1
    refine' ⟨1, fun j ↦ if j = 1 then 1 else 0, by simp, by simp, _⟩
    intro j hj
    simp [Finset.mem_Icc] at hj
    rcases hj with ⟨hj₁, hj₂⟩
    simp_all [abs_of_nonneg, abs_of_nonpos, pow_two]
    <;> norm_num
    <;> aesop
  · -- Case i = 2
    use 4
    use fun j => if j = 0 then 0 else if j = 1 then -1 else if j = 2 then -5 else if j = 3 then -14 else 2
    constructor
    · simp
    constructor
    · simp
    intro j hj
    simp [Finset.mem_Icc] at hj
    rcases hj with ⟨hj₁, hj₂⟩
    interval_cases j <;> norm_num [abs_of_nonneg, abs_of_nonpos, pow_two]
    <;> simp_all (config := {decide := true})
    <;> aesop
  · -- Case i = 3
    use 5
    use fun j => if j = 0 then 0 else if j = 1 then -1 else if j = 2 then 3 else if j = 3 then 12 else if j = 4 then 28 else 3
    constructor
    · simp
    constructor
    · simp
    intro j hj
    simp [Finset.mem_Icc] at hj
    rcases hj with ⟨hj₁, hj₂⟩
    interval_cases j <;> norm_num [abs_of_nonneg, abs_of_nonpos, pow_two]
    <;> simp_all (config := {decide := true})
    <;> aesop

lemma iii (i : ℕ) (h : ∃ n : ℕ, ∃ a : ℕ → ℤ,
    a 0 = 0 ∧
    a n = i ∧
    ∀ j ∈ Finset.Icc 1 n, |a j - a (j - 1)| = (j : ℤ) ^ 2) : ∃ n : ℕ, ∃ a : ℕ → ℤ,
    a 0 = 0 ∧
    a n = i + 4 ∧
    ∀ j ∈ Finset.Icc 1 n, |a j - a (j - 1)| = (j : ℤ) ^ 2 := by
  have h_main : ∃ n : ℕ, ∃ a : ℕ → ℤ, a 0 = 0 ∧ a n = ↑i + 4 ∧ ∀ j ∈ Finset.Icc 1 n, |a j - a (j - 1)| = (j : ℤ) ^ 2 := by
    obtain ⟨n, a, h₀, h₁, h₂⟩ := h
    use n + 4
    have h₃ : ∀ (k : ℕ), k ≤ n → (a k : ℤ) = a k := by intro k hk; simp
    have h₄ : (a n : ℤ) = i := by simpa using h₁
    -- We define the new function a' : ℕ → ℤ that extends the original function a.
    use fun m => if m ≤ n then a m else if m = n + 1 then (a n + (n + 1 : ℤ) ^ 2) else if m = n + 2 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) else if m = n + 3 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) else (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2)
    constructor
    · -- Prove a' 0 = 0
      simp_all [h₀]
      <;> norm_num
    · constructor
      · -- Prove a' (n + 4) = i + 4
        have h₅ : (n + 4 : ℕ) > n := by linarith
        have h₆ : (n + 4 : ℕ) ≠ n + 1 := by omega
        have h₇ : (n + 4 : ℕ) ≠ n + 2 := by omega
        have h₈ : (n + 4 : ℕ) ≠ n + 3 := by omega
        simp_all [Finset.mem_Icc, Nat.lt_succ_iff]
        <;> ring_nf at *
        <;> norm_num
        <;> simp_all [h₄]
        <;> ring_nf at *
        <;> norm_num
        <;> linarith
      · -- Prove ∀ j ∈ Finset.Icc 1 (n + 4), |a' j - a' (j - 1)| = (j : ℤ) ^ 2
        intro j hj
        have h₉ : j ∈ Finset.Icc 1 (n + 4) := hj
        have h₁₀ : 1 ≤ j ∧ j ≤ n + 4 := by simpa using Finset.mem_Icc.mp h₉
        have h₁₁ : j ≥ 1 := by linarith
        have h₁₂ : j ≤ n + 4 := by linarith
        have h₁₃ : j ≤ n ∨ j = n + 1 ∨ j = n + 2 ∨ j = n + 3 ∨ j = n + 4 := by
          omega
        rcases h₁₃ with (h₁₃ | h₁₃ | h₁₃ | h₁₃ | h₁₃)
        · -- Case j ≤ n
          have h₁₄ : j ≤ n := h₁₃
          have h₁₅ : j ∈ Finset.Icc 1 n := by
            exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩
          have h₁₆ : |(a j : ℤ) - (a (j - 1))| = (j : ℤ) ^ 2 := h₂ j h₁₅
          have h₁₇ : (if j ≤ n then a j else if j = n + 1 then (a n + (n + 1 : ℤ) ^ 2) else if j = n + 2 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) else if j = n + 3 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) else (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2)) = a j := by
            split_ifs <;> simp_all <;> omega
          have h₁₈ : (if (j - 1 : ℕ) ≤ n then a (j - 1) else if (j - 1 : ℕ) = n + 1 then (a n + (n + 1 : ℤ) ^ 2) else if (j - 1 : ℕ) = n + 2 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) else if (j - 1 : ℕ) = n + 3 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) else (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2)) = a (j - 1) := by
            split_ifs <;>
            (try omega) <;>
            (try
              {
                have h₁₉ : j ≥ 1 := by omega
                have h₂₀ : j ≤ n := by omega
                omega
              }) <;>
            (try omega)
          simp_all [h₁₇, h₁₈]
          <;>
          (try omega)
          ring_nf at *
          split_ifs at * with y1 y2 y3 y4 y5 y6 y7
          all_goals try omega -- this must kill off some goals
          all_goals try apply h₂ <;> (try assumption) <;> (try linarith) <;> (try nlinarith) <;> (try omega)
          all_goals try rw [← h₁₈ (by omega)]
        · -- Case j = n + 1
          have h₁₄ : j = n + 1 := h₁₃
          have h₁₅ : j ≤ n + 4 := by linarith
          have h₁₆ : (if j ≤ n then a j else if j = n + 1 then (a n + (n + 1 : ℤ) ^ 2) else if j = n + 2 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) else if j = n + 3 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) else (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2)) = (a n + (n + 1 : ℤ) ^ 2) := by
            simp [h₁₄]
            <;> norm_num
            <;> omega
          have h₁₇ : (if (j - 1 : ℕ) ≤ n then a (j - 1) else if (j - 1 : ℕ) = n + 1 then (a n + (n + 1 : ℤ) ^ 2) else if (j - 1 : ℕ) = n + 2 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) else if (j - 1 : ℕ) = n + 3 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) else (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2)) = a n := by
            have h₁₈ : (j - 1 : ℕ) = n := by omega
            simp [h₁₈]
            <;> norm_num
            <;> omega
          simp_all [h₁₆, h₁₇]
          <;>
          norm_num
          <;>
          cases' le_or_lt 0 ((n : ℤ) + 1) with h₁₉ h₁₉ <;>
          cases' le_or_lt 0 ((a n : ℤ)) with h₂₀ h₂₀ <;>
          simp_all [abs_of_nonneg, abs_of_neg, abs_of_nonpos, abs_of_pos, le_of_lt]
          <;>
          nlinarith
        · -- Case j = n + 2
          have h₁₄ : j = n + 2 := h₁₃
          have h₁₅ : j ≤ n + 4 := by linarith
          have h₁₆ : (if j ≤ n then a j else if j = n + 1 then (a n + (n + 1 : ℤ) ^ 2) else if j = n + 2 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) else if j = n + 3 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) else (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2)) = (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) := by
            simp [h₁₄]
            <;> norm_num
            <;> omega
          have h₁₇ : (if (j - 1 : ℕ) ≤ n then a (j - 1) else if (j - 1 : ℕ) = n + 1 then (a n + (n + 1 : ℤ) ^ 2) else if (j - 1 : ℕ) = n + 2 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) else if (j - 1 : ℕ) = n + 3 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) else (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2)) = (a n + (n + 1 : ℤ) ^ 2) := by
            have h₁₈ : (j - 1 : ℕ) = n + 1 := by omega
            simp [h₁₈]
            <;> norm_num
            <;> omega
          simp_all [h₁₆, h₁₇]
          <;>
          norm_num
          <;>
          cases' le_or_lt 0 ((n : ℤ) + 2) with h₁₉ h₁₉ <;>
          cases' le_or_lt 0 ((a n : ℤ) + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) with h₂₀ h₂₀ <;>
          cases' le_or_lt 0 ((a n : ℤ) + (n + 1 : ℤ) ^ 2) with h₂₁ h₂₁ <;>
          simp_all [abs_of_nonneg, abs_of_neg, abs_of_nonpos, abs_of_pos, le_of_lt]
          <;>
          nlinarith
        · -- Case j = n + 3
          have h₁₄ : j = n + 3 := h₁₃
          have h₁₅ : j ≤ n + 4 := by linarith
          have h₁₆ : (if j ≤ n then a j else if j = n + 1 then (a n + (n + 1 : ℤ) ^ 2) else if j = n + 2 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) else if j = n + 3 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) else (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2)) = (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) := by
            simp [h₁₄]
            <;> norm_num
            <;> omega
          have h₁₇ : (if (j - 1 : ℕ) ≤ n then a (j - 1) else if (j - 1 : ℕ) = n + 1 then (a n + (n + 1 : ℤ) ^ 2) else if (j - 1 : ℕ) = n + 2 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) else if (j - 1 : ℕ) = n + 3 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) else (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2)) = (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) := by
            have h₁₈ : (j - 1 : ℕ) = n + 2 := by omega
            simp [h₁₈]
            <;> norm_num
            <;> omega
          simp_all [h₁₆, h₁₇]
          <;>
          norm_num
          <;>
          cases' le_or_lt 0 ((n : ℤ) + 3) with h₁₉ h₁₉ <;>
          cases' le_or_lt 0 ((a n : ℤ) + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) with h₂₀ h₂₀ <;>
          cases' le_or_lt 0 ((a n : ℤ) + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) with h₂₁ h₂₁ <;>
          cases' le_or_lt 0 ((a n : ℤ) + (n + 1 : ℤ) ^ 2) with h₂₂ h₂₂ <;>
          simp_all [abs_of_nonneg, abs_of_neg, abs_of_nonpos, abs_of_pos, le_of_lt]
          <;>
          nlinarith
        · -- Case j = n + 4
          have h₁₄ : j = n + 4 := h₁₃
          have h₁₅ : j ≤ n + 4 := by linarith
          have h₁₆ : (if j ≤ n then a j else if j = n + 1 then (a n + (n + 1 : ℤ) ^ 2) else if j = n + 2 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) else if j = n + 3 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) else (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2)) = (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2) := by
            simp [h₁₄]
            <;> norm_num
            <;> omega
          have h₁₇ : (if (j - 1 : ℕ) ≤ n then a (j - 1) else if (j - 1 : ℕ) = n + 1 then (a n + (n + 1 : ℤ) ^ 2) else if (j - 1 : ℕ) = n + 2 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) else if (j - 1 : ℕ) = n + 3 then (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) else (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2)) = (a n + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) := by
            have h₁₈ : (j - 1 : ℕ) = n + 3 := by omega
            simp [h₁₈]
            <;> norm_num
            <;> omega
          simp_all [h₁₆, h₁₇]
          <;>
          norm_num
          <;>
          cases' le_or_lt 0 ((n : ℤ) + 4) with h₁₉ h₁₉ <;>
          cases' le_or_lt 0 ((a n : ℤ) + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2 + (n + 4 : ℤ) ^ 2) with h₂₀ h₂₀ <;>
          cases' le_or_lt 0 ((a n : ℤ) + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2 - (n + 3 : ℤ) ^ 2) with h₂₁ h₂₁ <;>
          cases' le_or_lt 0 ((a n : ℤ) + (n + 1 : ℤ) ^ 2 - (n + 2 : ℤ) ^ 2) with h₂₂ h₂₂ <;>
          cases' le_or_lt 0 ((a n : ℤ) + (n + 1 : ℤ) ^ 2) with h₂₃ h₂₃ <;>
          simp_all [abs_of_nonneg, abs_of_neg, abs_of_nonpos, abs_of_pos, le_of_lt]
          <;>
          nlinarith
  -- Now use h_main to get the result
  have h_final : ∃ n : ℕ, ∃ a : ℕ → ℤ, a 0 = 0 ∧ a n = ↑i + 4 ∧ ∀ j ∈ Finset.Icc 1 n, |a j - a (j - 1)| = (j : ℤ) ^ 2 := by
    exact h_main
  obtain ⟨n, a, ha₁, ha₂, ha₃⟩ := h_final
  refine' ⟨n, a, ha₁, _⟩
  constructor
  · -- Prove a n = i + 4
    simpa [Int.ofNat_add, Int.ofNat_one, Int.ofNat_zero] using ha₂
  · -- Prove ∀ j ∈ Finset.Icc 1 n, |a j - a (j - 1)| = (j : ℤ) ^ 2
    simpa using ha₃

lemma ijj {P : Nat -> Prop} (h : ∀ (i : ℕ), i < 4 → P i) (h1 : ∀ (i : ℕ), P i → P (i + 4)) : (∀ (i : ℕ), P i) := by 
  intro i
  have h2 : i % 4 < 4 := by
    omega
  have h3 : P (i % 4) := h (i % 4) h2
  have h4 : ∀ (n : ℕ), P (i % 4 + 4 * n) := by
    intro n
    induction n with
    | zero =>
      simp
      exact h3
    | succ n ih =>
      have h5 : P (i % 4 + 4 * n) := ih
      have h6 : P ( (i % 4 + 4 * n) + 4 ) := h1 (i % 4 + 4 * n) h5
      simp [show i % 4 + 4 * (n + 1) = (i % 4 + 4 * n) + 4 by omega] at *
      exact h6
  have h5 : i % 4 + 4 * (i / 4) = i := by
    omega
  have h6 : P (i % 4 + 4 * (i / 4)) := h4 (i / 4)
  rw [h5] at h6
  exact h6

lemma idd (h : (∀ (i : ℕ), i < 4 → ∃ n : ℕ, ∃ a : ℕ → ℤ,
    a 0 = 0 ∧
    a n = i ∧
    ∀ j ∈ Finset.Icc 1 n, |a j - a (j - 1)| = (j : ℤ) ^ 2)) (h1 : ∀ (i : ℕ) (h : ∃ n : ℕ, ∃ a : ℕ → ℤ,
    a 0 = 0 ∧
    a n = i ∧
    ∀ j ∈ Finset.Icc 1 n, |a j - a (j - 1)| = (j : ℤ) ^ 2), ∃ n : ℕ, ∃ a : ℕ → ℤ,
    a 0 = 0 ∧
    a n = i + 4 ∧
    ∀ j ∈ Finset.Icc 1 n, |a j - a (j - 1)| = (j : ℤ) ^ 2) : (∀ (i : ℕ), ∃ n : ℕ, ∃ a : ℕ → ℤ,
    a 0 = 0 ∧
    a n = i ∧
    ∀ j ∈ Finset.Icc 1 n, |a j - a (j - 1)| = (j : ℤ) ^ 2) := by
  apply ijj
  all_goals assumption

lemma imm (h : (∀ (i : ℕ), ∃ n : ℕ, ∃ a : ℕ → ℤ,
    a 0 = 0 ∧
    a n = i ∧
    ∀ i ∈ Finset.Icc 1 n, |a i - a (i - 1)| = (i : ℤ) ^ 2)) :
  (∀ b c : ℤ, ∃ n : ℕ, ∃ a : ℕ → ℤ,
    a 0 = b ∧
    a n = c ∧
    ∀ i ∈ Finset.Icc 1 n, |a i - a (i - 1)| = (i : ℤ) ^ 2) := by
  have h_nat_abs : ∀ (b c : ℤ), ∃ (n : ℕ), ∃ (a : ℕ → ℤ), a 0 = b ∧ a n = c ∧ (∀ i ∈ Finset.Icc 1 n, |a i - a (i - 1)| = (i : ℤ) ^ 2) := by
    intro b c
    have h₁ : ∃ (n : ℕ), ∃ (a : ℕ → ℤ), a 0 = 0 ∧ a n = (Int.natAbs (c - b) : ℤ) ∧ ∀ i ∈ Finset.Icc 1 n, |a i - a (i - 1)| = (i : ℤ) ^ 2 := by
      have h₂ : ∃ (n : ℕ), ∃ (a : ℕ → ℤ), a 0 = 0 ∧ a n = (Int.natAbs (c - b) : ℕ) ∧ ∀ i ∈ Finset.Icc 1 n, |a i - a (i - 1)| = (i : ℤ) ^ 2 := by
        apply h
      obtain ⟨n, a, ha₀, ha₁, ha₂⟩ := h₂
      refine' ⟨n, a, ha₀, _⟩
      constructor
      · -- Prove that `a n = (Int.natAbs (c - b) : ℤ)`
        norm_cast at ha₁ ⊢
        <;> simp_all
      · -- Prove the difference condition
        exact ha₂
    obtain ⟨n, a, ha₀, ha₁, ha₂⟩ := h₁
    -- Use the obtained sequence `a` to construct the desired sequence `a'`
    by_cases hbc : c - b ≥ 0
    · -- Case: c - b ≥ 0
      have h₃ : (Int.natAbs (c - b) : ℤ) = c - b := by
        rw [Int.natAbs_of_nonneg hbc]
      have h₄ : a n = c - b := by
        rw [h₃] at ha₁
        exact ha₁
      use n
      use fun j => a j + b
      constructor
      · -- Prove that `a' 0 = b`
        simp [ha₀]
      · constructor
        · -- Prove that `a' n = c`
          rw [h₄]
          <;> ring_nf <;> linarith
        · -- Prove the difference condition
          intro i hi
          have h₅ : |(a i + b) - (a (i - 1) + b)| = |a i - a (i - 1)| := by
            ring_nf
            <;> simp [abs_sub_comm]
            <;> ring_nf
            <;> simp [abs_sub_comm]
          rw [h₅]
          have h₆ : ∀ i ∈ Finset.Icc 1 n, |a i - a (i - 1)| = (i : ℤ) ^ 2 := ha₂
          exact h₆ i hi
    · -- Case: c - b < 0
      have h₃ : (Int.natAbs (c - b) : ℤ) = b - c := by
        have h₄ : c - b < 0 := by linarith
        have h₅ : Int.natAbs (c - b) = Int.natAbs (b - c) := by
          rw [← Int.natAbs_neg]
          <;> simp [Int.neg_sub]
        have h₆ : (Int.natAbs (c - b) : ℤ) = b - c := by
          rw [h₅]
          have h₇ : b - c > 0 := by
            omega
          have h₈ : Int.natAbs (b - c) = b - c := by
            rw [Int.natAbs_of_nonneg (by linarith)]
            <;> norm_cast
          rw [h₈]
          <;> norm_cast
          <;> omega
        exact h₆
      have h₄ : a n = b - c := by
        rw [h₃] at ha₁
        exact ha₁
      use n
      use fun j => b - a j
      constructor
      · -- Prove that `a' 0 = b`
        simp [ha₀]
      · constructor
        · -- Prove that `a' n = c`
          rw [h₄]
          <;> ring_nf <;> linarith
        · -- Prove the difference condition
          intro i hi
          have h₅ : |(b - a i) - (b - a (i - 1))| = |a i - a (i - 1)| := by
            ring_nf
            clear * -
            rw [show -a i + a (i - 1) = -(a i - a (i - 1)) by ring]
            rw [abs_neg]
          rw [h₅]
          have h₆ : ∀ i ∈ Finset.Icc 1 n, |a i - a (i - 1)| = (i : ℤ) ^ 2 := ha₂
          exact h₆ i hi
  exact h_nat_abs

/- 21. N3 (BUL) A finite sequence of integers $a_{0}, a_{1}, \ldots, a_{n}$ is called quadratic if for each $i \in\{1,2, \ldots, n\}$ we have the equality $\left|a_{i}-a_{i-1}\right|=i^{2}$. (a) Prove that for any two integers $b$ and $c$, there exist a natural number $n$ and a quadratic sequence with $a_{0}=b$ and $a_{n}=c$. -/
theorem number_theory_24696_1 (b c : ℤ) :
  ∃ n : ℕ, ∃ a : ℕ → ℤ,
    a 0 = b ∧
    a n = c ∧
    ∀ i ∈ Finset.Icc 1 n, |a i - a (i - 1)| = (i : ℤ) ^ 2 := by
  apply imm
  apply idd
  · apply rtt
  apply iii

theorem extracted_1 (i : ℕ) (a : ℕ → ℤ) (h : a 0 = 0) (h1 : a i = 1996)
  (h2 : ∀ (i_1 : ℕ), 1 ≤ i_1 → i_1 ≤ i → |a i_1 - a (i_1 - 1)| = ↑i_1 ^ 2) (j : ℕ) (hj : j <= i) : a j <= j * (j + 1) * (2 * j + 1) / 6 := by
  have h_sum_squares_div : ∀ n : ℕ, 6 ∣ n * (n + 1) * (2 * n + 1) := by
    intro n
    have h₁ : n * (n + 1) * (2 * n + 1) % 6 = 0 := by
      have h₂ : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
        omega
      rcases h₂ with (h₂ | h₂ | h₂ | h₂ | h₂ | h₂)
      · -- Case n ≡ 0 mod 6
        have h₃ : n % 6 = 0 := h₂
        have h₄ : n * (n + 1) * (2 * n + 1) % 6 = 0 := by
          have h₅ : n % 6 = 0 := h₃
          have h₆ : (n : ℕ) % 6 = 0 := by simpa using h₅
          have h₇ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
            have h₈ : (n : ℕ) % 6 = 0 := h₆
            have h₉ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
              simp [h₈, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt,
                Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
              <;> norm_num <;> ring_nf at h₈ ⊢ <;> omega
            exact h₉
          exact_mod_cast h₇
        exact h₄
      · -- Case n ≡ 1 mod 6
        have h₃ : n % 6 = 1 := h₂
        have h₄ : n * (n + 1) * (2 * n + 1) % 6 = 0 := by
          have h₅ : n % 6 = 1 := h₃
          have h₆ : (n : ℕ) % 6 = 1 := by simpa using h₅
          have h₇ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
            have h₈ : (n : ℕ) % 6 = 1 := h₆
            have h₉ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
              simp [h₈, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt,
                Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
              <;> norm_num <;> ring_nf at h₈ ⊢ <;> omega
            exact h₉
          exact_mod_cast h₇
        exact h₄
      · -- Case n ≡ 2 mod 6
        have h₃ : n % 6 = 2 := h₂
        have h₄ : n * (n + 1) * (2 * n + 1) % 6 = 0 := by
          have h₅ : n % 6 = 2 := h₃
          have h₆ : (n : ℕ) % 6 = 2 := by simpa using h₅
          have h₇ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
            have h₈ : (n : ℕ) % 6 = 2 := h₆
            have h₉ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
              simp [h₈, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt,
                Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
              <;> norm_num <;> ring_nf at h₈ ⊢ <;> omega
            exact h₉
          exact_mod_cast h₇
        exact h₄
      · -- Case n ≡ 3 mod 6
        have h₃ : n % 6 = 3 := h₂
        have h₄ : n * (n + 1) * (2 * n + 1) % 6 = 0 := by
          have h₅ : n % 6 = 3 := h₃
          have h₆ : (n : ℕ) % 6 = 3 := by simpa using h₅
          have h₇ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
            have h₈ : (n : ℕ) % 6 = 3 := h₆
            have h₉ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
              simp [h₈, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt,
                Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
              <;> norm_num <;> ring_nf at h₈ ⊢ <;> omega
            exact h₉
          exact_mod_cast h₇
        exact h₄
      · -- Case n ≡ 4 mod 6
        have h₃ : n % 6 = 4 := h₂
        have h₄ : n * (n + 1) * (2 * n + 1) % 6 = 0 := by
          have h₅ : n % 6 = 4 := h₃
          have h₆ : (n : ℕ) % 6 = 4 := by simpa using h₅
          have h₇ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
            have h₈ : (n : ℕ) % 6 = 4 := h₆
            have h₉ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
              simp [h₈, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt,
                Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
              <;> norm_num <;> ring_nf at h₈ ⊢ <;> omega
            exact h₉
          exact_mod_cast h₇
        exact h₄
      · -- Case n ≡ 5 mod 6
        have h₃ : n % 6 = 5 := h₂
        have h₄ : n * (n + 1) * (2 * n + 1) % 6 = 0 := by
          have h₅ : n % 6 = 5 := h₃
          have h₆ : (n : ℕ) % 6 = 5 := by simpa using h₅
          have h₇ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
            have h₈ : (n : ℕ) % 6 = 5 := h₆
            have h₉ : (n : ℕ) * (n + 1) * (2 * n + 1) % 6 = 0 := by
              simp [h₈, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt,
                Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
              <;> norm_num <;> ring_nf at h₈ ⊢ <;> omega
            exact h₉
          exact_mod_cast h₇
        exact h₄
    exact Nat.dvd_of_mod_eq_zero h₁
  
  have h_transformation : ∀ (j : ℕ), 1 ≤ j → (j - 1) * j * (2 * j - 1) + 6 * j ^ 2 = j * (j + 1) * (2 * j + 1) := by
    intro j hj₁
    have h₀ : j ≥ 1 := by omega
    cases j with
    | zero => contradiction
    | succ j' =>
      cases j' with
      | zero =>
        norm_num
      | succ j'' =>
        simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.mul_add, Nat.add_mul,
          Nat.mul_one, Nat.mul_zero, Nat.add_assoc]
        <;> ring_nf at * <;> norm_num <;> nlinarith
  
  have h_main : ∀ (k : ℕ), k ≤ i → a k ≤ k * (k + 1) * (2 * k + 1) / 6 := by
    intro k hk
    have h₀ : ∀ (n : ℕ), n ≤ i → a n ≤ n * (n + 1) * (2 * n + 1) / 6 := by
      intro n hn
      have h₁ : ∀ (n : ℕ), n ≤ i → a n ≤ n * (n + 1) * (2 * n + 1) / 6 := by
        intro n hn
        induction n using Nat.strong_induction_on with
        | h n ih =>
          match n with
          | 0 =>
            norm_num [h]
          | n + 1 =>
            have h₂ : a (n + 1) ≤ (n + 1) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by
              have h₃ : 1 ≤ (n + 1 : ℕ) := by
                omega
              have h₄ : (n + 1 : ℕ) ≤ i → |a (n + 1 : ℕ) - a ((n + 1 : ℕ) - 1)| = ((n + 1 : ℕ) : ℤ) ^ 2 := by
                intro h₅
                exact h2 (n + 1) (by omega) (by omega)
              have h₅ : (n + 1 : ℕ) ≤ i → a (n + 1 : ℕ) ≤ a (n : ℕ) + ((n + 1 : ℕ) : ℤ) ^ 2 := by
                intro h₅
                have h₆ : |a (n + 1 : ℕ) - a ((n + 1 : ℕ) - 1)| = ((n + 1 : ℕ) : ℤ) ^ 2 := h₄ h₅
                have h₇ : a (n + 1 : ℕ) - a ((n + 1 : ℕ) - 1) ≤ ((n + 1 : ℕ) : ℤ) ^ 2 := by
                  have h₈ : a (n + 1 : ℕ) - a ((n + 1 : ℕ) - 1) ≤ ((n + 1 : ℕ) : ℤ) ^ 2 := by
                    have h₉ : |a (n + 1 : ℕ) - a ((n + 1 : ℕ) - 1)| = ((n + 1 : ℕ) : ℤ) ^ 2 := h₆
                    have h₁₀ : a (n + 1 : ℕ) - a ((n + 1 : ℕ) - 1) ≤ ((n + 1 : ℕ) : ℤ) ^ 2 := by
                      have h₁₁ : a (n + 1 : ℕ) - a ((n + 1 : ℕ) - 1) ≤ |a (n + 1 : ℕ) - a ((n + 1 : ℕ) - 1)| := by
                        exact le_abs_self _
                      have h₁₂ : |a (n + 1 : ℕ) - a ((n + 1 : ℕ) - 1)| = ((n + 1 : ℕ) : ℤ) ^ 2 := h₉
                      linarith
                    exact h₁₀
                  exact h₈
                have h₉ : a (n + 1 : ℕ) ≤ a (n : ℕ) + ((n + 1 : ℕ) : ℤ) ^ 2 := by
                  have h₁₀ : a ((n + 1 : ℕ) - 1) = a n := by
                    simp [Nat.succ_eq_add_one, Nat.add_sub_cancel]
                  have h₁₁ : a (n + 1 : ℕ) - a ((n + 1 : ℕ) - 1) ≤ ((n + 1 : ℕ) : ℤ) ^ 2 := h₇
                  have h₁₂ : a (n + 1 : ℕ) ≤ a ((n + 1 : ℕ) - 1) + ((n + 1 : ℕ) : ℤ) ^ 2 := by
                    linarith
                  have h₁₃ : a ((n + 1 : ℕ) - 1) + ((n + 1 : ℕ) : ℤ) ^ 2 = a (n : ℕ) + ((n + 1 : ℕ) : ℤ) ^ 2 := by
                    simp [Nat.succ_eq_add_one, Nat.add_sub_cancel] at h₁₀ ⊢
                    <;> simp_all
                    <;> ring_nf at *
                    <;> omega
                  linarith
                exact h₉
              by_cases h₁₀ : (n + 1 : ℕ) ≤ i
              · -- Case: n + 1 ≤ i
                have h₁₁ : a (n + 1 : ℕ) ≤ a (n : ℕ) + ((n + 1 : ℕ) : ℤ) ^ 2 := by
                  exact h₅ h₁₀
                have h₁₂ : a (n : ℕ) ≤ n * (n + 1) * (2 * n + 1) / 6 := by
                  have h₁₃ : n ≤ i := by
                    omega
                  have h₁₄ : a n ≤ n * (n + 1) * (2 * n + 1) / 6 := by
                    have h₁₅ : n ≤ i := by
                      omega
                    exact ih n (by omega) h₁₅
                  exact h₁₄
                have h₁₅ : (n : ℤ) * (n + 1) * (2 * n + 1) / 6 + ((n + 1 : ℕ) : ℤ) ^ 2 ≤ (n + 1 : ℕ) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by
                  have h₁₆ : (n : ℕ) ≥ 0 := by
                    omega
                  have h₁₇ : (n : ℤ) * (n + 1) * (2 * n + 1) / 6 + ((n + 1 : ℕ) : ℤ) ^ 2 = (n + 1 : ℕ) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by
                    have h₁₈ : (n : ℕ) = n := by rfl
                    have h₁₉ : (n : ℕ) + 1 = n + 1 := by rfl
                    have h₂₀ : (n : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le n)
                    have h₂₁ : (n : ℤ) * (n + 1) * (2 * n + 1) / 6 + ((n + 1 : ℕ) : ℤ) ^ 2 = (n + 1 : ℕ) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by
                      have h₂₂ : 6 ∣ (n : ℕ) * (n + 1) * (2 * n + 1) := by
                        apply h_sum_squares_div
                      have h₂₃ : 6 ∣ (n + 1 : ℕ) * ((n + 1) + 1) * (2 * (n + 1) + 1) := by
                        apply h_sum_squares_div
                      have h₂₄ : (n : ℤ) * (n + 1) * (2 * n + 1) / 6 = ((n : ℕ) * (n + 1) * (2 * n + 1) / 6 : ℤ) := by
                        norm_cast
                        <;> simp [Int.ediv_eq_zero_of_lt]
                        <;> ring_nf
                        <;> norm_num
                        <;> omega
                      have h₂₅ : ((n + 1 : ℕ) : ℤ) ^ 2 = ((n + 1 : ℕ) ^ 2 : ℤ) := by
                        norm_cast
                      have h₂₆ : (n : ℤ) * (n + 1) * (2 * n + 1) / 6 + ((n + 1 : ℕ) : ℤ) ^ 2 = (n + 1 : ℕ) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by
                        have h₂₇ : (n : ℤ) * (n + 1) * (2 * n + 1) / 6 + ((n + 1 : ℕ) : ℤ) ^ 2 = (n + 1 : ℕ) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by
                          have h₂₈ := h_transformation (n + 1) (by omega)
                          norm_num at h₂₈ ⊢
                          <;>
                          (try omega) <;>
                          (try ring_nf at h₂₈ ⊢) <;>
                          (try norm_cast at h₂₈ ⊢) <;>
                          (try omega) <;>
                          (try
                            {
                              omega
                            })
                          <;>
                          (try
                            {
                              ring_nf at h₂₈ ⊢
                              <;>
                              omega
                            })
                          <;>
                          omega
                        exact h₂₇
                      exact h₂₆
                    exact h₂₁
                  omega
                have h₂₂ : a (n + 1 : ℕ) ≤ (n + 1 : ℕ) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by
                  have h₂₃ : a (n + 1 : ℕ) ≤ a (n : ℕ) + ((n + 1 : ℕ) : ℤ) ^ 2 := h₁₁
                  have h₂₄ : (a (n : ℕ) : ℤ) ≤ n * (n + 1) * (2 * n + 1) / 6 := by
                    exact_mod_cast h₁₂
                  have h₂₅ : (a (n : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ) ^ 2 ≤ (n : ℤ) * (n + 1) * (2 * n + 1) / 6 + ((n + 1 : ℕ) : ℤ) ^ 2 := by
                    linarith
                  have h₂₆ : (n : ℤ) * (n + 1) * (2 * n + 1) / 6 + ((n + 1 : ℕ) : ℤ) ^ 2 ≤ (n + 1 : ℕ) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by
                    exact h₁₅
                  have h₂₇ : (a (n + 1 : ℕ) : ℤ) ≤ (n + 1 : ℕ) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by
                    have h₂₈ : (a (n + 1 : ℕ) : ℤ) ≤ (a (n : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ) ^ 2 := by
                      exact_mod_cast h₁₁
                    have h₂₉ : (a (n : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ) ^ 2 ≤ (n : ℤ) * (n + 1) * (2 * n + 1) / 6 + ((n + 1 : ℕ) : ℤ) ^ 2 := by
                      linarith
                    have h₃₀ : (n : ℤ) * (n + 1) * (2 * n + 1) / 6 + ((n + 1 : ℕ) : ℤ) ^ 2 ≤ (n + 1 : ℕ) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by
                      exact h₁₅
                    have h₃₁ : (a (n + 1 : ℕ) : ℤ) ≤ (n + 1 : ℕ) * ((n + 1) + 1) * (2 * (n + 1) + 1) / 6 := by
                      linarith
                    exact_mod_cast h₃₁
                  exact_mod_cast h₂₇
                exact h₂₂
              · -- Case: n + 1 > i
                have h₁₁ : n + 1 > i := by omega
                have h₁₂ : n ≥ i := by omega
                have h₁₃ : n ≤ i := by
                  omega
                have h₁₄ : n = i := by omega
                subst h₁₄
                have h₁₅ : a j ≤ j * (j + 1) * (2 * j + 1) / 6 := by
                  have h₁₆ := h2 j
                  have h₁₇ := h2 1
                  have h₁₈ := h2 0
                  simp at h₁₆ h₁₇ h₁₈
                  <;>
                  (try omega) <;>
                  (try ring_nf at h₁₆ h₁₇ h₁₈ ⊢) <;>
                  (try norm_num at h₁₆ h₁₇ h₁₈ ⊢) <;>
                  (try omega) <;>
                  (try
                    {
                      simp_all [abs_eq_max_neg]
                      <;>
                      omega
                    })
                  <;>
                  (try
                    {
                      ring_nf at h₁₆ h₁₇ h₁₈ ⊢
                      <;>
                      omega
                    })
                  <;>
                  (try
                    {
                      simp_all [abs_eq_max_neg]
                      <;>
                      omega
                    })
                  <;>
                  (try
                    {
                      ring_nf at h₁₆ h₁₇ h₁₈ ⊢
                      <;>
                      omega
                    })
                omega
            push_cast
            assumption
          <;> try omega
          <;> try linarith
          <;> try ring_nf at *
          <;> try norm_num at *
          <;> try omega
      · apply h₁
        assumption
    exact h₀ _ hk
  
  have h_final : a j ≤ j * (j + 1) * (2 * j + 1) / 6 := by
    have h₁ : a j ≤ j * (j + 1) * (2 * j + 1) / 6 := by
      have h₂ : j ≤ i := hj
      have h₃ : a j ≤ j * (j + 1) * (2 * j + 1) / 6 := h_main j h₂
      exact h₃
    exact h₁
  
  exact h_final

theorem extracted_2 (i : ℕ) (a : ℕ → ℤ) (h : a 0 = 0) (h1 : a i = 1996)
  (h2 : ∀ (i_1 : ℕ), 1 ≤ i_1 → i_1 ≤ i → |a i_1 - a (i_1 - 1)| = ↑i_1 ^ 2) (j : ℕ) (hj : j <= i) : a j % 2 = (∑ x ∈ Finset.range (j + 1), x^2) % 2 := by
  have h_diff_mod : ∀ (k : ℕ), 1 ≤ k → k ≤ i → (a k % 2 : ℤ) = (a (k - 1) + k) % 2 := by
    intro k hk1 hk2
    have h3 : |a k - a (k - 1)| = (k : ℤ) ^ 2 := by
      have h4 : 1 ≤ k := hk1
      have h5 : k ≤ i := hk2
      have h6 : |a k - a (k - 1)| = (k : ℤ) ^ 2 := by
        have h7 : 1 ≤ k := hk1
        have h8 : k ≤ i := hk2
        have h9 : |a k - a (k - 1)| = (k : ℤ) ^ 2 := by
          have h10 : 1 ≤ k → k ≤ i → |a k - a (k - 1)| = (k : ℤ) ^ 2 := by
            intro h₁ h₂
            have h₁₁ := h2 k h₁ h₂
            simpa using h₁₁
          exact h10 h7 h8
        exact h9
      exact h6
    have h7 : a k % 2 = (a (k - 1) + k) % 2 := by
      have h8 : a k - a (k - 1) = (k : ℤ) ^ 2 ∨ a k - a (k - 1) = -((k : ℤ) ^ 2) := by
        have h9 : |a k - a (k - 1)| = (k : ℤ) ^ 2 := h3
        have h10 : a k - a (k - 1) = (k : ℤ) ^ 2 ∨ a k - a (k - 1) = -((k : ℤ) ^ 2) := by
          apply eq_or_eq_neg_of_abs_eq
          <;> simp_all [abs_eq]
          <;> ring_nf at *
          <;> simp_all
        exact h10
      have h11 : a k % 2 = (a (k - 1) + k) % 2 := by
        cases h8 with
        | inl h8 =>
          have h12 : a k - a (k - 1) = (k : ℤ) ^ 2 := h8
          have h13 : a k = a (k - 1) + (k : ℤ) ^ 2 := by linarith
          have h14 : (a k : ℤ) % 2 = (a (k - 1) + k) % 2 := by
            rw [h13]
            have h15 : ((k : ℤ) ^ 2 : ℤ) % 2 = (k : ℤ) % 2 := by
              have h16 : (k : ℤ) % 2 = 0 ∨ (k : ℤ) % 2 = 1 := by
                omega
              rcases h16 with (h16 | h16) <;> simp [h16, pow_two, Int.mul_emod, Int.add_emod]
            have h17 : ((a (k - 1) + (k : ℤ) ^ 2 : ℤ) % 2 : ℤ) = ((a (k - 1) + (k : ℤ)) % 2 : ℤ) := by
              have h18 : ((k : ℤ) ^ 2 : ℤ) % 2 = (k : ℤ) % 2 := by
                have h19 : (k : ℤ) % 2 = 0 ∨ (k : ℤ) % 2 = 1 := by
                  omega
                rcases h19 with (h19 | h19) <;> simp [h19, pow_two, Int.mul_emod, Int.add_emod]
              omega
            omega
          exact_mod_cast h14
        | inr h8 =>
          have h12 : a k - a (k - 1) = -((k : ℤ) ^ 2) := h8
          have h13 : a k = a (k - 1) - (k : ℤ) ^ 2 := by linarith
          have h14 : (a k : ℤ) % 2 = (a (k - 1) + k) % 2 := by
            rw [h13]
            have h15 : ((-(k : ℤ) ^ 2 : ℤ) % 2 : ℤ) = (k : ℤ) % 2 := by
              have h16 : (k : ℤ) % 2 = 0 ∨ (k : ℤ) % 2 = 1 := by
                omega
              rcases h16 with (h16 | h16) <;> simp [h16, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
              <;> norm_num <;> omega
            have h17 : ((a (k - 1) - (k : ℤ) ^ 2 : ℤ) % 2 : ℤ) = ((a (k - 1) + (k : ℤ)) % 2 : ℤ) := by
              have h18 : ((-(k : ℤ) ^ 2 : ℤ) % 2 : ℤ) = (k : ℤ) % 2 := by
                have h19 : (k : ℤ) % 2 = 0 ∨ (k : ℤ) % 2 = 1 := by
                  omega
                rcases h19 with (h19 | h19) <;> simp [h19, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
                <;> norm_num <;> omega
              omega
            omega
          exact_mod_cast h14
      exact h11
    exact h7
  
  have h_sum_mod : ∀ (j : ℕ), j ≤ i → (a j % 2 : ℤ) = (∑ x ∈ Finset.range (j + 1), (x : ℤ)) % 2 := by
    intro j hj_le_i
    have h₀ : ∀ (n : ℕ), n ≤ i → (a n % 2 : ℤ) = (∑ x in Finset.range (n + 1), (x : ℤ)) % 2 := by
      intro n hn_le_i
      induction n using Nat.strong_induction_on with
      | h n ih =>
        match n with
        | 0 =>
          norm_num [Finset.sum_range_succ] at *
          <;> simp [h]
          <;> norm_num
        | k + 1 =>
          have h₁ : (a (k + 1) % 2 : ℤ) = (a (k + 1 - 1) + (k + 1 : ℤ)) % 2 := by
            have h₂ : 1 ≤ k + 1 := by omega
            have h₃ : (k + 1 : ℕ) ≤ i := by omega
            have h₄ := h_diff_mod (k + 1) (by omega) h₃
            simpa using h₄
          have h₂ : (a (k + 1 - 1) % 2 : ℤ) = (∑ x in Finset.range (k + 1 - 1 + 1), (x : ℤ)) % 2 := by
            have h₃ : k + 1 - 1 ≤ i := by omega
            have h₄ : k + 1 - 1 < k + 1 := by omega
            have h₅ : k + 1 - 1 ≤ i := by omega
            exact ih (k + 1 - 1) (by omega) (by omega)
          have h₃ : (∑ x in Finset.range (k + 1 + 1), (x : ℤ)) = (∑ x in Finset.range (k + 1), (x : ℤ)) + (k + 1 : ℤ) := by
            simp [Finset.sum_range_succ, add_comm]
            <;> simp_all [Finset.sum_range_succ]
            rw [add_comm]
            simp_all [Finset.sum_range_succ]
          have h₄ : (a (k + 1) % 2 : ℤ) = (∑ x in Finset.range (k + 1 + 1), (x : ℤ)) % 2 := by
            have h₅ : (a (k + 1) % 2 : ℤ) = (a (k + 1 - 1) + (k + 1 : ℤ)) % 2 := h₁
            have h₆ : (a (k + 1 - 1) % 2 : ℤ) = (∑ x in Finset.range (k + 1 - 1 + 1), (x : ℤ)) % 2 := h₂
            have h₇ : (∑ x in Finset.range (k + 1 + 1), (x : ℤ)) = (∑ x in Finset.range (k + 1), (x : ℤ)) + (k + 1 : ℤ) := h₃
            have h₈ : (a (k + 1) % 2 : ℤ) = ((∑ x in Finset.range (k + 1 - 1 + 1), (x : ℤ)) % 2 + (k + 1 : ℤ)) % 2 := by
              calc
                (a (k + 1) % 2 : ℤ) = (a (k + 1 - 1) + (k + 1 : ℤ)) % 2 := h₅
                _ = ((a (k + 1 - 1) % 2 : ℤ) + (k + 1 : ℤ)) % 2 := by
                  simp [Int.add_emod, Int.emod_emod]
                _ = ((∑ x in Finset.range (k + 1 - 1 + 1), (x : ℤ)) % 2 + (k + 1 : ℤ)) % 2 := by rw [h₆]
            have h₉ : (∑ x in Finset.range (k + 1 - 1 + 1), (x : ℤ)) % 2 = (∑ x in Finset.range (k + 1), (x : ℤ)) % 2 := by
              have h₁₀ : k + 1 - 1 + 1 = k + 1 := by omega
              rw [h₁₀]
            rw [h₈, h₉]
            have h₁₀ : (∑ x in Finset.range (k + 1), (x : ℤ)) % 2 = (∑ x in Finset.range (k + 1), (x : ℤ)) % 2 := rfl
            have h₁₁ : ((∑ x in Finset.range (k + 1), (x : ℤ)) % 2 + (k + 1 : ℤ)) % 2 = ((∑ x in Finset.range (k + 1), (x : ℤ)) + (k + 1 : ℤ)) % 2 := by
              simp [Int.add_emod, Int.emod_emod]
            have h₁₂ : ((∑ x in Finset.range (k + 1), (x : ℤ)) + (k + 1 : ℤ)) % 2 = (∑ x in Finset.range (k + 1 + 1), (x : ℤ)) % 2 := by
              rw [h₃]
            rw [h₁₁, h₁₂]
            <;> simp [Int.add_emod, Int.emod_emod]
          exact h₄
      <;> simp_all [Finset.sum_range_succ, Int.add_emod, Int.emod_emod]
      <;> ring_nf at *
      <;> omega
    exact h₀ j hj_le_i
  
  have h_sum_eq : ∀ (j : ℕ), (∑ x ∈ Finset.range (j + 1), (x : ℤ)) % 2 = (∑ x ∈ Finset.range (j + 1), (x : ℤ)^2) % 2 := by
    intro j
    have h₁ : (∑ x in Finset.range (j + 1), (x : ℤ)) % 2 = (∑ x in Finset.range (j + 1), (x : ℤ) ^ 2) % 2 := by
      have h₂ : ∀ (x : ℕ), (x : ℤ) % 2 = (x : ℤ) ^ 2 % 2 := by
        intro x
        have h₃ : (x : ℤ) % 2 = 0 ∨ (x : ℤ) % 2 = 1 := by
          omega
        rcases h₃ with (h₃ | h₃)
        · -- Case: (x : ℤ) % 2 = 0
          have h₄ : (x : ℤ) ^ 2 % 2 = 0 := by
            have h₅ : (x : ℤ) % 2 = 0 := h₃
            have h₆ : (x : ℤ) ^ 2 % 2 = 0 := by
              have h₇ : (x : ℤ) % 2 = 0 := h₅
              have h₈ : (x : ℤ) ^ 2 % 2 = 0 := by
                norm_num [pow_two, Int.mul_emod, h₇]
              exact h₈
            exact h₆
          omega
        · -- Case: (x : ℤ) % 2 = 1
          have h₄ : (x : ℤ) ^ 2 % 2 = 1 := by
            have h₅ : (x : ℤ) % 2 = 1 := h₃
            have h₆ : (x : ℤ) ^ 2 % 2 = 1 := by
              have h₇ : (x : ℤ) % 2 = 1 := h₅
              have h₈ : (x : ℤ) ^ 2 % 2 = 1 := by
                norm_num [pow_two, Int.mul_emod, h₇]
              exact h₈
            exact h₆
          omega
      have h₅ : (∑ x in Finset.range (j + 1), (x : ℤ)) % 2 = (∑ x in Finset.range (j + 1), (x : ℤ) ^ 2) % 2 := by
        calc
          (∑ x in Finset.range (j + 1), (x : ℤ)) % 2 = (∑ x in Finset.range (j + 1), ((x : ℤ) % 2)) % 2 := by
            simp [Finset.sum_int_mod]
          _ = (∑ x in Finset.range (j + 1), ((x : ℤ) ^ 2 % 2)) % 2 := by
            apply congr_arg (fun x => x % 2)
            apply Finset.sum_congr rfl
            intro x hx
            rw [h₂ x]
          _ = (∑ x in Finset.range (j + 1), (x : ℤ) ^ 2) % 2 := by
            simp [Finset.sum_int_mod]
            <;> simp_all [Finset.sum_range_succ, Int.add_emod]
            <;> norm_num
            <;> omega
      exact h₅
    exact h₁
  
  have h_final : (a j % 2 : ℤ) = (∑ x ∈ Finset.range (j + 1), x^2) % 2 := by
    have h₃ : (a j % 2 : ℤ) = (∑ x ∈ Finset.range (j + 1), (x : ℤ)) % 2 := by
      apply h_sum_mod j hj
    have h₄ : (∑ x ∈ Finset.range (j + 1), (x : ℤ)) % 2 = (∑ x ∈ Finset.range (j + 1), (x : ℤ) ^ 2) % 2 := by
      apply h_sum_eq j
    have h₅ : (a j % 2 : ℤ) = (∑ x ∈ Finset.range (j + 1), (x : ℤ) ^ 2) % 2 := by
      calc
        (a j % 2 : ℤ) = (∑ x ∈ Finset.range (j + 1), (x : ℤ)) % 2 := by rw [h₃]
        _ = (∑ x ∈ Finset.range (j + 1), (x : ℤ) ^ 2) % 2 := by rw [h₄]
    have h₆ : (∑ x ∈ Finset.range (j + 1), x ^ 2 : ℤ) = (∑ x ∈ Finset.range (j + 1), (x : ℤ) ^ 2) := by
      simp [Finset.sum_range_succ, pow_two]
    rw [h₆] at *
    norm_num
    assumption
  
  have h₇ : a j % 2 = (∑ x ∈ Finset.range (j + 1), x ^ 2) % 2 := by
    exact_mod_cast h_final
  exact h₇
  <;> aesop

theorem my_favorite_theorem (j : ℕ) :
    (∑ x ∈ Finset.range (j + 1), x^2) = (j*(j + 1)*(2*j + 1))/6 := by
  have h_base : (∑ x ∈ Finset.range (0 + 1), x^2) = (0*(0 + 1)*(2*0 + 1))/6 := by
    simp [Finset.sum_range_succ]
    <;> norm_num
  
  have h_inductive_step : ∀ (m : ℕ), (∑ x ∈ Finset.range (m + 1), x^2) = (m*(m + 1)*(2*m + 1))/6 → (∑ x ∈ Finset.range (m + 1 + 1), x^2) = ((m + 1)*((m + 1) + 1)*(2*(m + 1) + 1))/6 := by
    intro m hm
    have h₁ : (∑ x in Finset.range (m + 1 + 1), x ^ 2) = (∑ x in Finset.range (m + 1), x ^ 2) + (m + 1) ^ 2 := by
      simp [Finset.sum_range_succ, add_assoc]
      <;> ring_nf
      <;> simp_all [Finset.sum_range_succ, add_assoc]
      <;> ring_nf
      <;> linarith
    rw [h₁]
    rw [hm]
    have h₂ : (m : ℕ) * (m + 1) * (2 * m + 1) / 6 + (m + 1) ^ 2 = ((m + 1) * ((m + 1) + 1) * (2 * (m + 1) + 1)) / 6 := by
      have h₃ : (m : ℕ) * (m + 1) * (2 * m + 1) + 6 * (m + 1) ^ 2 = (m + 1) * ((m + 1) + 1) * (2 * (m + 1) + 1) := by
        cases m with
        | zero => norm_num
        | succ m =>
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          <;> ring_nf at *
          <;> omega
      have h₄ : (m : ℕ) * (m + 1) * (2 * m + 1) % 6 = 0 := by
        have h₅ : (m : ℕ) * (m + 1) * (2 * m + 1) % 6 = 0 := by
          have h₆ : (m : ℕ) % 6 = 0 ∨ (m : ℕ) % 6 = 1 ∨ (m : ℕ) % 6 = 2 ∨ (m : ℕ) % 6 = 3 ∨ (m : ℕ) % 6 = 4 ∨ (m : ℕ) % 6 = 5 := by omega
          rcases h₆ with (h₆ | h₆ | h₆ | h₆ | h₆ | h₆) <;>
          simp [h₆, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_self, zero_add, Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm, Nat.pow_succ]
          <;> ring_nf at * <;> norm_num at * <;>
          (try omega) <;>
          (try
            {
              ring_nf at *
              <;> omega
            }) <;>
          (try
            {
              omega
            }) <;>
          (try
            {
              ring_nf at *
              <;> omega
            }) <;>
          (try
            {
              omega
            }) <;>
          (try
            {
              ring_nf at *
              <;> omega
            }) <;>
          (try
            {
              omega
            })
        exact h₅
      have h₅ : (m : ℕ) * (m + 1) * (2 * m + 1) / 6 + (m + 1) ^ 2 = ((m + 1) * ((m + 1) + 1) * (2 * (m + 1) + 1)) / 6 := by
        have h₆ : (m : ℕ) * (m + 1) * (2 * m + 1) + 6 * (m + 1) ^ 2 = (m + 1) * ((m + 1) + 1) * (2 * (m + 1) + 1) := by
          exact h₃
        have h₇ : (m : ℕ) * (m + 1) * (2 * m + 1) % 6 = 0 := by
          exact h₄
        have h₈ : ((m : ℕ) * (m + 1) * (2 * m + 1) / 6) * 6 = (m : ℕ) * (m + 1) * (2 * m + 1) := by
          have h₉ : (m : ℕ) * (m + 1) * (2 * m + 1) = ((m : ℕ) * (m + 1) * (2 * m + 1) / 6) * 6 + (m : ℕ) * (m + 1) * (2 * m + 1) % 6 := by
            omega
          omega
        have h₉ : ((m + 1) * ((m + 1) + 1) * (2 * (m + 1) + 1)) % 6 = 0 := by
          have h₁₀ : (m + 1 : ℕ) % 6 = 0 ∨ (m + 1 : ℕ) % 6 = 1 ∨ (m + 1 : ℕ) % 6 = 2 ∨ (m + 1 : ℕ) % 6 = 3 ∨ (m + 1 : ℕ) % 6 = 4 ∨ (m + 1 : ℕ) % 6 = 5 := by omega
          rcases h₁₀ with (h₁₀ | h₁₀ | h₁₀ | h₁₀ | h₁₀ | h₁₀) <;>
          simp [h₁₀, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_self, zero_add, Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm, Nat.pow_succ]
          <;> ring_nf at * <;> norm_num at * <;>
          (try omega) <;>
          (try
            {
              ring_nf at *
              <;> omega
            }) <;>
          (try
            {
              omega
            }) <;>
          (try
            {
              ring_nf at *
              <;> omega
            }) <;>
          (try
            {
              omega
            }) <;>
          (try
            {
              ring_nf at *
              <;> omega
            }) <;>
          (try
            {
              omega
            })
        have h₁₀ : ((m + 1) * ((m + 1) + 1) * (2 * (m + 1) + 1) / 6) * 6 = (m + 1) * ((m + 1) + 1) * (2 * (m + 1) + 1) := by
          have h₁₁ : (m + 1 : ℕ) * ((m + 1) + 1) * (2 * (m + 1) + 1) = ((m + 1 : ℕ) * ((m + 1) + 1) * (2 * (m + 1) + 1) / 6) * 6 + ((m + 1 : ℕ) * ((m + 1) + 1) * (2 * (m + 1) + 1) % 6) := by
            omega
          omega
        have h₁₁ : (m : ℕ) * (m + 1) * (2 * m + 1) / 6 + (m + 1) ^ 2 = (m + 1 : ℕ) * ((m + 1) + 1) * (2 * (m + 1) + 1) / 6 := by
          have h₁₂ : (m : ℕ) * (m + 1) * (2 * m + 1) / 6 * 6 + 6 * ((m + 1 : ℕ) ^ 2) = (m + 1 : ℕ) * ((m + 1) + 1) * (2 * (m + 1) + 1) := by
            nlinarith
          omega
        exact h₁₁
      exact h₅
    have h₃ : (m : ℕ) * (m + 1) * (2 * m + 1) / 6 + (m + 1) ^ 2 = ((m + 1) * ((m + 1) + 1) * (2 * (m + 1) + 1)) / 6 := by
      exact h₂
    omega
  
  have h_main : (∑ x ∈ Finset.range (j + 1), x^2) = (j*(j + 1)*(2*j + 1))/6 := by
    have h₀ : ∀ n : ℕ, (∑ x in Finset.range (n + 1), x ^ 2) = (n * (n + 1) * (2 * n + 1)) / 6 := by
      intro n
      induction n with
      | zero => simp [h_base]
      | succ n ih =>
        -- Use the inductive hypothesis to prove the statement for n + 1
        have h₁ := h_inductive_step n ih
        simpa [Finset.sum_range_succ, Nat.succ_eq_add_one, add_assoc] using h₁
    -- Apply the general result to j
    have h₁ := h₀ j
    simpa using h₁
  
  exact h_main

/- (b) Find the smallest natural number $n$ for which there exists a quadratic sequence with $a_{0}=0$ and $a_{n}=1996$. -/
theorem number_theory_24696_2 : IsLeast { n | ∃ a : ℕ → ℤ,
  a 0 = 0 ∧
  a n = 1996 ∧
  ∀ i ∈ Finset.Icc 1 n, |a i - a (i - 1)| = (i : ℤ) ^ 2 } 19 := by
  constructor
  · exists (fun n => [0, 1, 5, 14, -2, -27, 9, 58, 122, 203, 303, 424, 568, 737, 541, 766, 1022, 1311, 1635, 1996].getD n 0)
  rw [mem_lowerBounds]
  simp
  intros i a h h1 h2
  have clr : 18 ≤ i := by
    have dl := extracted_1 i a (by assumption) (by assumption) (by assumption) i (by exact Nat.le_refl i)
    rw [h1] at dl
    clear * - dl
    by_contra ls
    interval_cases i <;> revert dl <;> native_decide
  -- now we prove the parity
  have dl := extracted_2 i a (by assumption) (by assumption) (by assumption) i (by exact Nat.le_refl i)
  obtain rfl | kxs : i = 18 ∨ 19 ≤ i := by clear * - clr; omega
  · rw [h1, my_favorite_theorem] at dl
    norm_num at dl
  exact kxs
