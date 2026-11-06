import Mathlib

theorem number_theory_322535 (a : ℕ) :
    (∑ i ∈ Finset.range 2002, a^(i + 1)) % 10 ≠ 4 := by
  have h1 : a % 10 = 0 ∨ a % 10 = 1 ∨ a % 10 = 2 ∨ a % 10 = 3 ∨ a % 10 = 4 ∨ a % 10 = 5 ∨ a % 10 = 6 ∨ a % 10 = 7 ∨ a % 10 = 8 ∨ a % 10 = 9 := by
    omega
  rcases h1 with (h | h | h | h | h | h | h | h | h | h)
  · -- a % 10 = 0
    have h2 : ∀ i : ℕ, (a ^ (i + 1)) % 10 = 0 := by
      intro i
      simp [Nat.pow_mod, h, Nat.mul_mod, Nat.add_mod]
    have h3 : (∑ i in Finset.range 2002, a ^ (i + 1)) % 10 = 0 := by
      rw [Finset.sum_nat_mod]
      have h4 : (∑ i in Finset.range 2002, (a ^ (i + 1)) % 10) = 0 := by
        rw [Finset.sum_eq_zero]
        intro i hi
        specialize h2 i
        omega
      omega
    omega
  · -- a % 10 = 1
    have h2 : ∀ i : ℕ, (a ^ (i + 1)) % 10 = 1 := by
      intro i
      simp [Nat.pow_mod, h, Nat.mul_mod, Nat.add_mod]
    have h3 : (∑ i in Finset.range 2002, a ^ (i + 1)) % 10 = 2 := by
      rw [Finset.sum_nat_mod]
      have h4 : (∑ i in Finset.range 2002, (a ^ (i + 1)) % 10) = 2002 := by
        rw [Finset.sum_congr rfl (fun i _ => h2 i)]
        native_decide
      omega
    omega
  · -- a % 10 = 2
    have h1 : ∀ n : ℕ, (a ^ n) % 10 = (2 ^ n) % 10 := by
      intro n
      have h2 : a % 10 = 2 := h
      have h3 : ∀ m : ℕ, (a ^ m) % 10 = (2 ^ m) % 10 := by
        intro m
        induction m with
        | zero =>
          simp
        | succ m ih =>
          simp [Nat.pow_succ, Nat.mul_mod, h2] at ih ⊢
          omega
      specialize h3 n
      simpa using h3
    have h4 : (∑ i in Finset.range 2002, a ^ (i + 1)) % 10 = 6 := by
      rw [Finset.sum_nat_mod]
      rw [Finset.sum_congr rfl (fun i _ => h1 (i + 1))]
      native_decide
    omega
  · -- a % 10 = 3
    have h1 : ∀ n : ℕ, (a ^ n) % 10 = (3 ^ n) % 10 := by
      intro n
      have h2 : a % 10 = 3 := h
      have h3 : ∀ m : ℕ, (a ^ m) % 10 = (3 ^ m) % 10 := by
        intro m
        induction m with
        | zero =>
          simp
        | succ m ih =>
          simp [Nat.pow_succ, Nat.mul_mod, h2] at ih ⊢
          omega
      specialize h3 n
      simpa using h3
    have h4 : (∑ i in Finset.range 2002, a ^ (i + 1)) % 10 = 2 := by
      rw [Finset.sum_nat_mod]
      rw [Finset.sum_congr rfl (fun i _ => h1 (i + 1))]
      native_decide
    omega
  · -- a % 10 = 4
    have h1 : ∀ n : ℕ, (a ^ n) % 10 = (4 ^ n) % 10 := by
      intro n
      have h2 : a % 10 = 4 := h
      have h3 : ∀ m : ℕ, (a ^ m) % 10 = (4 ^ m) % 10 := by
        intro m
        induction m with
        | zero =>
          simp
        | succ m ih =>
          simp [Nat.pow_succ, Nat.mul_mod, h2] at ih ⊢
          omega
      specialize h3 n
      simpa using h3
    have h4 : (∑ i in Finset.range 2002, a ^ (i + 1)) % 10 = 0 := by
      rw [Finset.sum_nat_mod]
      rw [Finset.sum_congr rfl (fun i _ => h1 (i + 1))]
      native_decide
    omega
  · -- a % 10 = 5
    have h1 : ∀ n : ℕ, (a ^ n) % 10 = (5 ^ n) % 10 := by
      intro n
      have h2 : a % 10 = 5 := h
      have h3 : ∀ m : ℕ, (a ^ m) % 10 = (5 ^ m) % 10 := by
        intro m
        induction m with
        | zero =>
          simp
        | succ m ih =>
          simp [Nat.pow_succ, Nat.mul_mod, h2] at ih ⊢
          omega
      specialize h3 n
      simpa using h3
    have h4 : (∑ i in Finset.range 2002, a ^ (i + 1)) % 10 = 0 := by
      rw [Finset.sum_nat_mod]
      rw [Finset.sum_congr rfl (fun i _ => h1 (i + 1))]
      native_decide
    omega
  · -- a % 10 = 6
    have h1 : ∀ n : ℕ, (a ^ n) % 10 = (6 ^ n) % 10 := by
      intro n
      have h2 : a % 10 = 6 := h
      have h3 : ∀ m : ℕ, (a ^ m) % 10 = (6 ^ m) % 10 := by
        intro m
        induction m with
        | zero =>
          simp
        | succ m ih =>
          simp [Nat.pow_succ, Nat.mul_mod, h2] at ih ⊢
          omega
      specialize h3 n
      simpa using h3
    have h4 : (∑ i in Finset.range 2002, a ^ (i + 1)) % 10 = 2 := by
      rw [Finset.sum_nat_mod]
      rw [Finset.sum_congr rfl (fun i _ => h1 (i + 1))]
      native_decide
    omega
  · -- a % 10 = 7
    have h1 : ∀ n : ℕ, (a ^ n) % 10 = (7 ^ n) % 10 := by
      intro n
      have h2 : a % 10 = 7 := h
      have h3 : ∀ m : ℕ, (a ^ m) % 10 = (7 ^ m) % 10 := by
        intro m
        induction m with
        | zero =>
          simp
        | succ m ih =>
          simp [Nat.pow_succ, Nat.mul_mod, h2] at ih ⊢
          omega
      specialize h3 n
      simpa using h3
    have h4 : (∑ i in Finset.range 2002, a ^ (i + 1)) % 10 = 6 := by
      rw [Finset.sum_nat_mod]
      rw [Finset.sum_congr rfl (fun i _ => h1 (i + 1))]
      native_decide
    omega
  · -- a % 10 = 8
    have h1 : ∀ n : ℕ, (a ^ n) % 10 = (8 ^ n) % 10 := by
      intro n
      have h2 : a % 10 = 8 := h
      have h3 : ∀ m : ℕ, (a ^ m) % 10 = (8 ^ m) % 10 := by
        intro m
        induction m with
        | zero =>
          simp
        | succ m ih =>
          simp [Nat.pow_succ, Nat.mul_mod, h2] at ih ⊢
          omega
      specialize h3 n
      simpa using h3
    have h4 : (∑ i in Finset.range 2002, a ^ (i + 1)) % 10 = 2 := by
      rw [Finset.sum_nat_mod]
      rw [Finset.sum_congr rfl (fun i _ => h1 (i + 1))]
      native_decide
    omega
  · -- a % 10 = 9
    have h1 : ∀ n : ℕ, (a ^ n) % 10 = (9 ^ n) % 10 := by
      intro n
      have h2 : a % 10 = 9 := h
      have h3 : ∀ m : ℕ, (a ^ m) % 10 = (9 ^ m) % 10 := by
        intro m
        induction m with
        | zero =>
          simp
        | succ m ih =>
          simp [Nat.pow_succ, Nat.mul_mod, h2] at ih ⊢
          omega
      specialize h3 n
      simpa using h3
    have h4 : (∑ i in Finset.range 2002, a ^ (i + 1)) % 10 = 0 := by
      rw [Finset.sum_nat_mod]
      rw [Finset.sum_congr rfl (fun i _ => h1 (i + 1))]
      native_decide
    omega