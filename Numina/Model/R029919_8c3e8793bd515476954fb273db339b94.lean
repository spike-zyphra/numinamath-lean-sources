import Mathlib

theorem number_theory_171241 (g : ℕ → ℕ) (h₀ : ∀ n, ∑ d in n.divisors, g d = Nat.totient n) :
    g 50 = 0 := by 
  -- First, let's compute g 1.
  have h1 : g 1 = Nat.totient 1 := by 
    have h11 := h₀ 1 
    have h12 : ∑ d in (1 : ℕ).divisors, g d = g 1 := by 
      simp [Finset.sum_singleton]
    rw [h12] at h11 
    all_goals try tauto
  -- φ(1) = 1.
  have ht1 : Nat.totient 1 = 1 := by 
    rw [Nat.totient_one]
  -- Therefore g(1) = 1.
  have h11 : g 1 = 1 := by 
    rw [ht1] at h1 
    all_goals try tauto
  -- From h₀ for n = 2, there are two divisors {1, 2} so we get g 1 + g 2 = φ(2) = 1
  -- φ(2) = 1.
  have h2 : g 2 = 0 := by 
    have h21 := h₀ 2 
    have h22 := h₀ 1 
    have h211 : (2 : ℕ).divisors = {1, 2} := by decide 
    have h222 : (1 : ℕ).divisors = {1} := by decide 
    rw [h211] at h21 
    rw [h222] at h22 
    have eq1 : g 1 = 1 := h11 
    simp [Finset.sum_insert, Finset.sum_singleton] at h21 h22 
    all_goals 
      norm_num [Nat.totient] at h21 h22 
      all_goals 
        omega 
  -- For n = 5, divisors are {1, 5} so g 1 + g 5 = φ(5) = 4. Since g 1 = 1, we get g 5 = 3
  have h3 : g 5 = 3 := by 
    have h31 := h₀ 5 
    have h32 : g 1 = 1 := h11 
    have h311 : (5 : ℕ).divisors = {1, 5} := by decide 
    rw [h311] at h31 
    simp [Finset.sum_insert, Finset.sum_singleton] at h31 
    have ht5 : Nat.totient 5 = 4 := by 
      native_decide 
    norm_num [ht5] at h31 
    all_goals 
      omega 
  -- For n = 10, divisors are {1, 2, 5, 10}, so sum g over these = φ(10) = 4. We get g 10 = 0
  have h4 : g 10 = 0 := by 
    have h41 := h₀ 10 
    have h42 : g 1 = 1 := h11 
    have h43 : g 2 = 0 := h2 
    have h44 : g 5 = 3 := h3 
    have h411 : (10 : ℕ).divisors = {1, 2, 5, 10} := by decide 
    rw [h411] at h41 
    simp [Finset.sum_insert, Finset.sum_singleton] at h41 
    have ht10 : Nat.totient 10 = 4 := by 
      native_decide 
    norm_num [ht10] at h41 
    omega 
  -- For n = 25, divisors are {1, 5, 25}, so sum g over these = φ(25) = 20. We get g 25 = 16
  have h5 : g 25 = 16 := by 
    have h51 := h₀ 25 
    have h52 : g 1 = 1 := h11 
    have h53 : g 5 = 3 := h3 
    have h511 : (25 : ℕ).divisors = {1, 5, 25} := by decide 
    rw [h511] at h51 
    simp [Finset.sum_insert, Finset.sum_singleton] at h51 
    have ht25 : Nat.totient 25 = 20 := by 
      native_decide 
    norm_num [ht25] at h51 
    omega 
  -- For n = 50, we need g 50. The equation is sum over divisors {1, 2, 5, 10, 25, 50} of g d = φ(50) = 20
  -- Substitute all known values: 1 + 0 + 3 + 0 + 16 + g 50 = 20. Therefore g 50 = 0
  have h6 : g 50 = 0 := by 
    have h61 := h₀ 50 
    have h62 : g 1 = 1 := h11 
    have h63 : g 2 = 0 := h2 
    have h64 : g 5 = 3 := h3 
    have h65 : g 10 = 0 := h4 
    have h66 : g 25 = 16 := h5 
    have h611 : (50 : ℕ).divisors = {1, 2, 5, 10, 25, 50} := by decide 
    rw [h611] at h61 
    simp [Finset.sum_insert, Finset.sum_singleton] at h61 
    have ht50 : Nat.totient 50 = 20 := by 
      native_decide 
    norm_num [ht50] at h61 
    omega 
  exact h6
  all_goals tauto 
  <;> nlinarith 
  <;> tauto 
  <;> nlinarith