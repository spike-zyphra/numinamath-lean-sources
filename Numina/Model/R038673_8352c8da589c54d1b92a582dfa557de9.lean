import Mathlib

theorem number_theory_23102 (u1 u2 : ℕ) (u1pos : u1 > 0) (u2pos : u2 > 0)
    (u1ltu2 : u1 < u2) (modeq_u1 : 14 * u1 ≡ 46 [MOD 100])
    (modeq_u2 : 14 * u2 ≡ 46 [MOD 100])
    (two_smallest: ∀u:ℕ, 14 * u ≡ 46 [MOD 100] → u ≠ u1 → u ≥ u2) :
    (u1 + u2) / 2 = 64 := by
  have h1 : u1 ≤ 39 := by
    by_contra h
    push_neg at h
    have h39 : 14 * 39 ≡ 46 [MOD 100] := by
      norm_num [Nat.ModEq]
    have h2 := two_smallest 39 h39
    have hne : (39 : ℕ) ≠ u1 := by
      omega
    have h3 := h2 hne
    omega
  have h3 : u1 = 39 := by
    by_cases hle : u1 < 39
    · -- Assume u1 < 39.
      have h5 : u1 < 39 := by linarith
      have hne : 14 * u1 ≡ 46 [MOD 100] := modeq_u1
      interval_cases u1 <;> norm_num [Nat.ModEq] at hne
      all_goals omega
    have h4 : u1 ≥ 39 := by omega
    have h4 : u1 ≥ 39 := by omega
    omega
  have h2 : u2 ≥ 89 := by
    by_contra h
    push_neg at h
    have hne : 14 * u2 ≡ 46 [MOD 100] := modeq_u2
    interval_cases u2 <;> norm_num [Nat.ModEq] at hne
    all_goals omega
  have h4 : u2 = 89 := by
    have h5 : u1 = 39 := h3
    have h89 : 14 * 89 ≡ 46 [MOD 100] := by
      norm_num [Nat.ModEq]
    have h89ge : 89 ≥ u2 := by
      apply two_smallest 89 h89
      have hne89 : (89 : ℕ) ≠ u1 := by
        omega
      simpa using hne89
    have h89eq : u2 ≥ 89 := h2
    omega
  calc
    (u1 + u2) / 2 = (39 + 89) / 2 := by rw [h3, h4]
    _ = 128 / 2 := by norm_num
    _ = 64 := by norm_num