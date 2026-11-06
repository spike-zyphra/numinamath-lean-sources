import Mathlib

/-
Prove that for digits d1,d2,d3,d4,d5 ∈ {0,…,9} with d1 ≠ 0, if
  (10000·d1 + 1000·d2 + 100·d3 + 10·d4 + d5) ≡ 0 (mod 9) and ≡ 0 (mod 11),
  10·d2 + d4 = 26, 9 ∣ (10·d4 + d5), and 9 ∣ (10·d1 + d2), then the five‐digit number 10000·d1 + 1000·d2 + 100·d3 + 10·d4 + d5 must be 72963.
-/

theorem unique_solution
  (d1 d2 d3 d4 d5 : ℕ) (p1 : d1 < 10) (p2 : d2 < 10) (p3 : d3 < 10) (p4 : d4 < 10) (p5 : d5 < 10)
  (h0 : d1 ≠ 0)
  (h1 : (10000*d1 + 1000*d2 + 100*d3 + 10*d4 + d5) % 9 = 0)
  (h2 : (10000*d1 + 1000*d2 + 100*d3 + 10*d4 + d5) % 11 = 0)
  (h3 : 10*d2 + d4 = 26)
  (h4 : 9 ∣ (10*d4 + d5))
  (h5 : 9 ∣ (10*d1 + d2)) :
  10000*d1 + 1000*d2 + 100*d3 + 10*d4 + d5 = 72963 := by
  -- First solve d2 and d4 from h3 (d2d4 = 26)
  have d2_eq_2_d4_eq_6 : d2 = 2 ∧ d4 = 6 := by
    interval_cases d2
    interval_cases d4
    all_goals omega
  obtain ⟨d2_eq,d4_eq⟩ := d2_eq_2_d4_eq_6
  rw [d4_eq] at h4

  -- Solve d5 from h4 (9 | 60 + d5)
  have cong_d5_mod9 : 60 + d5 ≡ 0 [MOD 9] := by exact Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat h4)
  have d5_mod9 : d5 % 9 = 3 := by
    have : 60 % 9 = 6 := by norm_num
    omega
  have d5_eq : d5 = 3 := by
    interval_cases d5
    all_goals omega

  -- Solve d1 from h5 (9 | 10*d1 + 2)
  rw [d2_eq] at h5
  have cong_d1_mod9 : 10 * d1 ≡ 7 [MOD 9] := by
    have h': (10 * d1 + 2) ≡ 0 [MOD 9] := by
      simpa [Nat.modEq_zero_iff_dvd] using h5
    exact Nat.ModEq.add_right_cancel' 2 h'
  have d1_eq : d1 = 7 := by
    interval_cases d1
    all_goals omega

  -- Solve d3 from h2 (11 | 72063 + 100*d3)
  have N_no_d3 : 10000*d1 + 1000*d2 + 100*d3 + 10*d4 + d5
    = 72063 + 100*d3 := by rw[d4_eq,d2_eq,d5_eq,d1_eq];ring
  have h_mod11 : (72063 + 100*d3) ≡ 0 [MOD 11] := by
    exact Nat.ModEq.symm (Nat.ModEq.trans (id (Eq.symm h2)) (congrFun (congrArg HMod.hMod N_no_d3) 11))
  have d3_eq : d3 = 9 := by
    interval_cases d3
    all_goals omega

  -- Final calculation
  calc
    10000*d1 + 1000*d2 + 100*d3 + 10*d4 + d5
      = 10000*7 + 1000*2 + 100*9 + 10*6 + 3 := by simp [d1_eq, d2_eq, d3_eq, d4_eq, d5_eq]
    _ = 72963 := by norm_num
