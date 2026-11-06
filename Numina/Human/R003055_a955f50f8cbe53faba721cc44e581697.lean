import Mathlib

/-N is the set of positive integers. M is the set of non-negative integers. f: N → M is a function such that f(10) = 0, f(n) = 0 if the last digit of n is 3, f(mn) = f(m) + f(n). Find f(1984) and f(1985).-/
theorem number_theory_148993 (f : ℕ → ℕ) (h₀ : ∀ n, f (10 * n + 3) = 0)
    (h₁ : f 10 = 0) (h₂ : ∀ m n, f (m * n) = f m + f n) :
    f 1984 = 0 ∧ f 1985 = 0 := by
  -- we have $1984 = 2 ^ 6 * 31$ and $1985 = 5 * 397$ 
  -- first we cauculate $f(2)=0$ and $f(5)=0$ through $2 * 5 = 10$ and $f(10)=0$.
  have h10 : f 10 = f 2 + f 5 := by
    rw [h₂ 2 5]
  rw [h₁] at h10
  have h2 : f 2 = 0 := by
    omega
  have h5 : f 5 = 0 := by 
    omega
  -- because $3193=31*103$ and the last digit of $3193,1103$ is both $3$, the value of $f(31)$ is zero.
  have h31 : f 31 = 0 := by
    have h3193 : f 3193 = 0 := h₀ 319
    have h3193_eq : f 3193 = f 31 + f 103 := by
      rw [h₂ 31 103]
    have h103 : f 103 = 0 := h₀ 10
    rw [h3193] at h3193_eq
    rw [h103] at h3193_eq
    omega
  have h397 : f 397 = 0 := by
    have h3573 : f 3573 = 0 := h₀ 357
    have h3573_eq : f 3573 = f 397 + f 9 := by
      rw [h₂ 397 9]
    have h9 : f 9 = 0 := by
      have h3 : f 3 = 0 := h₀ 0
      have h9_eq : f 9 = f 3 + f 3 := by
        rw [h₂ 3 3]
      rw [h3] at h9_eq
      omega
    rw [h3573] at h3573_eq
    rw [h9] at h3573_eq
    omega
  have h1984 : f 1984 = 0 := by
    have h1984_eq : f 1984 = f (2^6 * 31) := by
      norm_num
    rw [h1984_eq]
    have h1984_eq2 : f (2^6 * 31) = f (2^6) + f 31 := by 
      rw [h₂ (2^6) 31]
    rw [h1984_eq2]
    -- we use $f(mn) = f(m) + f(n)$ to calculate $f(2^6)$
    have h2_pow6 : f (2^6) = 0 := by
      have h2_pow1 : f 2 = 0 := h2
      have h4 : f 4 = f 2 + f 2 := by 
        rw [h₂ 2 2]
      have h4_val : f 4 = 0 := by 
        omega
      have h8 : f 8 = f 4 + f 2 := by 
        rw [h₂ 4 2]
      have h8_val : f 8 = 0 := by 
        omega
      have h16 : f 16 = f 8 + f 2 := by 
        rw [h₂ 8 2]
      have h16_val : f 16 = 0 := by 
        omega
      have h32 : f 32 = f 16 + f 2 := by 
        rw [h₂ 16 2]
      have h32_val : f 32 = 0 := by 
        omega
      have h64 : f 64 = f 32 + f 2 := by 
        rw [h₂ 32 2]
      have h64_val : f 64 = 0 := by 
        omega
      have h2_pow6 : f (2^6) = 0 := by 
        norm_num at h64_val ⊢
        exact h64_val
      exact h2_pow6
    rw [h2_pow6, h31]
  have h1985 : f 1985 = 0 := by 
    have h1985_eq : f 1985 = f 5 + f 397 := by 
      rw [h₂ 5 397]
    rw [h5, h397] at h1985_eq
    omega
  exact ⟨h1984, h1985⟩