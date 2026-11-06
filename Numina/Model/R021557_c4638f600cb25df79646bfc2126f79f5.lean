import Mathlib

noncomputable def f (n : ℕ) : ℕ := match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => (f (n + 1) + f n) % 3

theorem number_theory_287218 : ∑ i in Finset.Icc 2017 2024, f i = 9 := by
  have h1 : ∀ (n : ℕ), f (n + 8) = f n := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [f]
    | succ n =>
      cases n with
      | zero =>
        simp [f]
      | succ n =>
        have h4 : f (n + 2 + 8) = f (n + 2) := by
          have h5 : f (n + 8) = f n := ih n (by omega)
          have h6 : f ((n + 1) + 8) = f (n + 1) := ih (n + 1) (by omega)
          simp [f] at h5 h6 ⊢
          all_goals 
            omega
        simpa using h4

  have h17 : f 2017 = 1 := by
    have h18 : ∀ (k : ℕ), f (8 * k + 1) = 1 := by
      intro k
      induction k with
      | zero =>
        norm_num [f]
      | succ k ih =>
        have h20 : 8 * (k + 1) + 1 = (8 * k + 1) + 8 := by 
          omega
        rw [h20]
        have h21 : f ((8 * k + 1) + 8) = f (8 * k + 1) := by
          apply h1
        rw [h21, ih]
    have h19 : 2017 = 8 * 252 + 1 := by omega
    rw [h19] at *
    apply h18 252

  have h18 : f 2018 = 1 := by
    have h19 : ∀ (k : ℕ), f (8 * k + 2) = 1 := by
      intro k
      induction k with
      | zero =>
        norm_num [f]
      | succ k ih =>
        have h20 : 8 * (k + 1) + 2 = (8 * k + 2) + 8 := by 
          omega
        rw [h20]
        have h21 : f ((8 * k + 2) + 8) = f (8 * k + 2) := by
          apply h1
        rw [h21, ih]
    have h20 : 2018 = 8 * 252 + 2 := by omega
    rw [h20] at *
    apply h19 252

  have h19 : f 2019 = 2 := by
    have h20 : ∀ (k : ℕ), f (8 * k + 3) = 2 := by
      intro k
      induction k with
      | zero =>
        norm_num [f]
      | succ k ih =>
        have h21 : 8 * (k + 1) + 3 = (8 * k + 3) + 8 := by 
          omega
        rw [h21]
        have h22 : f ((8 * k + 3) + 8) = f (8 * k + 3) := by
          apply h1
        rw [h22, ih]
    have h23 : 2019 = 8 * 252 + 3 := by omega
    rw [h23] at *
    apply h20 252

  have h20 : f 2020 = 0 := by
    have h21 : ∀ (k : ℕ), f (8 * k + 4) = 0 := by
      intro k
      induction k with
      | zero =>
        norm_num [f]
      | succ k ih =>
        have h22 : 8 * (k + 1) + 4 = (8 * k + 4) + 8 := by 
          omega
        rw [h22]
        have h23 : f ((8 * k + 4) + 8) = f (8 * k + 4) := by
          apply h1
        rw [h23, ih]
    have h24 : 2020 = 8 * 252 + 4 := by omega
    rw [h24] at *
    apply h21 252

  have h21 : f 2021 = 2 := by
    have h22 : ∀ (k : ℕ), f (8 * k + 5) = 2 := by
      intro k
      induction k with
      | zero =>
        norm_num [f]
      | succ k ih =>
        have h23 : 8 * (k + 1) + 5 = (8 * k + 5) + 8 := by 
          omega
        rw [h23]
        have h24 : f ((8 * k + 5) + 8) = f (8 * k + 5) := by
          apply h1
        rw [h24, ih]
    have h25 : 2021 = 8 * 252 + 5 := by omega
    rw [h25] at *
    apply h22 252

  have h22 : f 2022 = 2 := by
    have h23 : ∀ (k : ℕ), f (8 * k + 6) = 2 := by
      intro k
      induction k with
      | zero =>
        norm_num [f]
      | succ k ih =>
        have h24 : 8 * (k + 1) + 6 = (8 * k + 6) + 8 := by 
          omega
        rw [h24]
        have h25 : f ((8 * k + 6) + 8) = f (8 * k + 6) := by
          apply h1
        rw [h25, ih]
    have h26 : 2022 = 8 * 252 + 6 := by omega
    rw [h26] at *
    apply h23 252

  have h23 : f 2023 = 1 := by
    have h24 : ∀ (k : ℕ), f (8 * k + 7) = 1 := by
      intro k
      induction k with
      | zero =>
        norm_num [f]
      | succ k ih =>
        have h25 : 8 * (k + 1) + 7 = (8 * k + 7) + 8 := by 
          omega
        rw [h25]
        have h26 : f ((8 * k + 7) + 8) = f (8 * k + 7) := by
          apply h1
        rw [h26, ih]
    have h27 : 2023 = 8 * 252 + 7 := by omega
    rw [h27] at *
    apply h24 252

  have h24 : f 2024 = 0 := by
    have h25 : ∀ (k : ℕ), f (8 * k + 8) = 0 := by
      intro k
      induction k with
      | zero =>
        norm_num [f]
      | succ k ih =>
        have h26 : 8 * (k + 1) + 8 = (8 * k + 8) + 8 := by 
          omega
        rw [h26]
        have h27 : f ((8 * k + 8) + 8) = f (8 * k + 8) := by
          apply h1
        rw [h27, ih]
    have h28 : 2024 = 8 * 252 + 8 := by omega
    rw [h28] at *
    apply h25 252

  calc
    ∑ i in Finset.Icc 2017 2024, f i
        = f 2017 + f 2018 + f 2019 + f 2020 + f 2021 + f 2022 + f 2023 + f 2024 := by
          norm_num [Finset.sum_Icc_succ_top]
    _ = 1 + 1 + 2 + 0 + 2 + 2 + 1 + 0 := by 
      rw [h17, h18, h19, h20, h21, h22, h23, h24]
    _ = 9 := by 
      norm_num