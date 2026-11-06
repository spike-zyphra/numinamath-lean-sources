import Mathlib

theorem number_theory_226569 (n : ℕ) (hn : n > 0) :
    5 ∣ ∑ i ∈ Finset.Icc 1 4, i^n ↔ ¬(4 ∣ n) := by
  constructor
  · -- Assume 5 divides the sum, prove n is not divisible by 4
    intro h
    by_contra h1
    have h2 : 4 ∣ n := by 
      simpa using h1
    have h3 : n % 4 = 0 := by 
      omega
    have h4 : (∑ i ∈ Finset.Icc 1 4, i ^ n) % 5 = 0 := by 
      omega
    -- Compute each term mod 5 when n is divisible by 4
    have h6 : (1 ^ n) % 5 = 1 := by
      have h1 : ∀ k, (1 ^ (4 * k + 0)) % 5 = 1 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
          all_goals omega
      have : n = 4 * (n / 4) + n % 4 := by 
        omega
      rw [show n % 4 = 0 by omega] at this
      rw [this]
      apply h1 (n / 4)
    have h7 : (2 ^ n) % 5 = 1 := by
      have h2 : ∀ k, (2 ^ (4 * k + 0)) % 5 = 1 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
          all_goals omega
      have : n = 4 * (n / 4) + n % 4 := by 
        omega
      rw [show n % 4 = 0 by omega] at this
      rw [this]
      apply h2 (n / 4)
    have h8 : (3 ^ n) % 5 = 1 := by
      have h3 : ∀ k, (3 ^ (4 * k + 0)) % 5 = 1 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
          all_goals omega
      have : n = 4 * (n / 4) + n % 4 := by 
        omega
      rw [show n % 4 = 0 by omega] at this
      rw [this]
      apply h3 (n / 4)
    have h9 : (4 ^ n) % 5 = 1 := by
      have h4 : ∀ k, (4 ^ (4 * k + 0)) % 5 = 1 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
          all_goals omega
      have : n = 4 * (n / 4) + n % 4 := by 
        omega
      rw [show n % 4 = 0 by omega] at this
      rw [this]
      apply h4 (n / 4)
    have h10 : (∑ i ∈ Finset.Icc 1 4, i ^ n) % 5 = 4 := by 
      simp [Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, h6, h7, h8, h9] <;> omega
    omega
  · -- Assume n is not divisible by 4, prove 5 divides the sum
    intro h
    have h1 : ¬ (4 ∣ n) := h
    have h2 : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · -- Case n % 4 = 1
      have h3 : (1 ^ n) % 5 = 1 := by
        have h1 : ∀ k, (1 ^ (4 * k + 1)) % 5 = 1 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 1 by omega] at this
        rw [this]
        apply h1 (n / 4)
      have h4 : (2 ^ n) % 5 = 2 := by
        have h2 : ∀ k, (2 ^ (4 * k + 1)) % 5 = 2 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 1 by omega] at this
        rw [this]
        apply h2 (n / 4)
      have h5 : (3 ^ n) % 5 = 3 := by
        have h3 : ∀ k, (3 ^ (4 * k + 1)) % 5 = 3 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 1 by omega] at this
        rw [this]
        apply h3 (n / 4)
      have h6 : (4 ^ n) % 5 = 4 := by
        have h4 : ∀ k, (4 ^ (4 * k + 1)) % 5 = 4 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 1 by omega] at this
        rw [this]
        apply h4 (n / 4)
      have h7 : (∑ i ∈ Finset.Icc 1 4, i ^ n) % 5 = 0 := by
        simp [Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, h3, h4, h5, h6] <;> omega
      omega
    · -- Case n % 4 = 2
      have h3 : (1 ^ n) % 5 = 1 := by
        have h1 : ∀ k, (1 ^ (4 * k + 2)) % 5 = 1 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 2 by omega] at this
        rw [this]
        apply h1 (n / 4)
      have h4 : (2 ^ n) % 5 = 4 := by
        have h2 : ∀ k, (2 ^ (4 * k + 2)) % 5 = 4 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 2 by omega] at this
        rw [this]
        apply h2 (n / 4)
      have h5 : (3 ^ n) % 5 = 4 := by
        have h3 : ∀ k, (3 ^ (4 * k + 2)) % 5 = 4 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 2 by omega] at this
        rw [this]
        apply h3 (n / 4)
      have h6 : (4 ^ n) % 5 = 1 := by
        have h4 : ∀ k, (4 ^ (4 * k + 2)) % 5 = 1 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 2 by omega] at this
        rw [this]
        apply h4 (n / 4)
      have h7 : (∑ i ∈ Finset.Icc 1 4, i ^ n) % 5 = 0 := by
        simp [Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, h3, h4, h5, h6] <;> omega
      omega
    · -- Case n % 4 = 3
      have h3 : (1 ^ n) % 5 = 1 := by
        have h1 : ∀ k, (1 ^ (4 * k + 3)) % 5 = 1 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 3 by omega] at this
        rw [this]
        apply h1 (n / 4)
      have h4 : (2 ^ n) % 5 = 3 := by
        have h2 : ∀ k, (2 ^ (4 * k + 3)) % 5 = 3 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 3 by omega] at this
        rw [this]
        apply h2 (n / 4)
      have h5 : (3 ^ n) % 5 = 2 := by
        have h3 : ∀ k, (3 ^ (4 * k + 3)) % 5 = 2 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 3 by omega] at this
        rw [this]
        apply h3 (n / 4)
      have h6 : (4 ^ n) % 5 = 4 := by
        have h4 : ∀ k, (4 ^ (4 * k + 3)) % 5 = 4 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢
            all_goals omega
        have : n = 4 * (n / 4) + (n % 4) := by 
          omega
        rw [show n % 4 = 3 by omega] at this
        rw [this]
        apply h4 (n / 4)
      have h7 : (∑ i ∈ Finset.Icc 1 4, i ^ n) % 5 = 0 := by
        simp [Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, h3, h4, h5, h6] <;> omega
      omega