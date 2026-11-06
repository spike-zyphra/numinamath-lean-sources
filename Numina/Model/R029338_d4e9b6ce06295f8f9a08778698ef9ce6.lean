import Mathlib

theorem number_theory_106440 :
    ∀ n : ℤ, 6 ∣ n * (n + 1) ∨ n * (n + 1) % 18 = 2 := by
  intro n
  have h1 : n % 18 = 0 ∨ n % 18 = 1 ∨ n % 18 = 2 ∨ n % 18 = 3 ∨ n % 18 = 4 ∨ n % 18 = 5 ∨
    n % 18 = 6 ∨ n % 18 = 7 ∨ n % 18 = 8 ∨ n % 18 = 9 ∨ n % 18 = 10 ∨ n % 18 = 11 ∨
    n % 18 = 12 ∨ n % 18 = 13 ∨ n % 18 = 14 ∨ n % 18 = 15 ∨ n % 18 = 16 ∨ n % 18 = 17 := by 
    omega 
  rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h)

  · -- Case n ≡ 0 mod 18
    have h2 : n * (n + 1) % 18 = 0 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3 
  · -- Case n ≡ 1 mod 18
    have h2 : n * (n + 1) % 18 = 2 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    right 
    exact h2 
  · -- Case n ≡ 2 mod 18
    have h2 : n * (n + 1) % 18 = 6 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3 
  · -- Case n ≡ 3 mod 18
    have h2 : n * (n + 1) % 18 = 12 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3 
  · -- Case n ≡ 4 mod 18
    have h2 : n * (n + 1) % 18 = 2 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    right 
    exact h2 
  · -- Case n ≡ 5 mod 18
    have h2 : n * (n + 1) % 18 = 12 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3 
  · -- Case n ≡ 6 mod 18
    have h2 : n * (n + 1) % 18 = 6 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3 
  · -- Case n ≡ 7 mod 18
    have h2 : n * (n + 1) % 18 = 2 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    right 
    exact h2 
  · -- Case n ≡ 8 mod 18
    have h2 : n * (n + 1) % 18 = 0 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3 
  · -- Case n ≡ 9 mod 18
    have h2 : n * (n + 1) % 18 = 0 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3 
  · -- Case n ≡ 10 mod 18
    have h2 : n * (n + 1) % 18 = 2 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    right 
    exact h2 
  · -- Case n ≡ 11 mod 18
    have h2 : n * (n + 1) % 18 = 6 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3 
  · -- Case n ≡ 12 mod 18
    have h2 : n * (n + 1) % 18 = 12 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3 
  · -- Case n ≡ 13 mod 18
    have h2 : n * (n + 1) % 18 = 2 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    right 
    exact h2 
  · -- Case n ≡ 14 mod 18
    have h2 : n * (n + 1) % 18 = 12 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3 
  · -- Case n ≡ 15 mod 18
    have h2 : n * (n + 1) % 18 = 6 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3 
  · -- Case n ≡ 16 mod 18
    have h2 : n * (n + 1) % 18 = 2 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    right 
    exact h2 
  · -- Case n ≡ 17 mod 18
    have h2 : n * (n + 1) % 18 = 0 := by 
      simp [h, Int.add_emod, Int.mul_emod] 
    have h3 : 6 ∣ n * (n + 1) := by 
      omega 
    left 
    exact h3