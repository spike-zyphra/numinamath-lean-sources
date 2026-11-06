import Mathlib
/-Theorem: Let $K$ be a positive integer. If the remainder of $K$ when divided by 9 is $r$, and $r \in \{2,3,5,6,8\}$, then there does not exist a natural number $n$ such that the sum of the digits of $n^2$ (in base 10) equals $K$.-/
theorem number_theory_637365 (K r : ℕ) (hr : r ∈ ({2, 3, 5, 6, 8} : Set ℕ)) (hK1 : K % 9 = r) :
    ¬∃ n, (Nat.digits 10 (n ^ 2)).sum = K := by 
  rcases hr with (rfl | rfl | rfl | rfl | rfl)
  · -- r = 2
    intro h
    rcases h with ⟨n, hn⟩
    have h1 : K % 9 = 2 := by 
      simp [hK1]
    have h2 : (Nat.digits 10 (n ^ 2)).sum % 9 = K % 9 := by 
      rw [hn]
    have h3 : (Nat.digits 10 (n ^ 2)).sum % 9 = n ^ 2 % 9 := by
      rw [Nat.modEq_nine_digits_sum (n ^ 2)]
    rw [h3] at h2
    rw [h1] at h2
    have h4 : n ^ 2 % 9 = 0 ∨ n ^ 2 % 9 = 1 ∨ n ^ 2 % 9 = 4 ∨ n ^ 2 % 9 = 7 := by
      have h : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
        omega
      rcases h with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
    omega
  · -- r = 3
    intro h
    rcases h with ⟨n, hn⟩
    have h1 : K % 9 = 3 := by 
      simp [hK1]
    have h2 : (Nat.digits 10 (n ^ 2)).sum % 9 = K % 9 := by 
      rw [hn]
    have h3 : (Nat.digits 10 (n ^ 2)).sum % 9 = n ^ 2 % 9 := by
      rw [Nat.modEq_nine_digits_sum (n ^ 2)]
    rw [h3] at h2
    rw [h1] at h2
    have h4 : n ^ 2 % 9 = 0 ∨ n ^ 2 % 9 = 1 ∨ n ^ 2 % 9 = 4 ∨ n ^ 2 % 9 = 7 := by
      have h : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
        omega
      rcases h with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
    omega
  · -- r = 5
    intro h
    rcases h with ⟨n, hn⟩
    have h1 : K % 9 = 5 := by 
      simp [hK1]
    have h2 : (Nat.digits 10 (n ^ 2)).sum % 9 = K % 9 := by 
      rw [hn]
    have h3 : (Nat.digits 10 (n ^ 2)).sum % 9 = n ^ 2 % 9 := by
      rw [Nat.modEq_nine_digits_sum (n ^ 2)]
    rw [h3] at h2
    rw [h1] at h2
    have h4 : n ^ 2 % 9 = 0 ∨ n ^ 2 % 9 = 1 ∨ n ^ 2 % 9 = 4 ∨ n ^ 2 % 9 = 7 := by
      have h : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
        omega
      rcases h with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
    omega
  · -- r = 6
    intro h
    rcases h with ⟨n, hn⟩
    have h1 : K % 9 = 6 := by 
      simp [hK1]
    have h2 : (Nat.digits 10 (n ^ 2)).sum % 9 = K % 9 := by 
      rw [hn]
    have h3 : (Nat.digits 10 (n ^ 2)).sum % 9 = n ^ 2 % 9 := by
      rw [Nat.modEq_nine_digits_sum (n ^ 2)]
    rw [h3] at h2
    rw [h1] at h2
    have h4 : n ^ 2 % 9 = 0 ∨ n ^ 2 % 9 = 1 ∨ n ^ 2 % 9 = 4 ∨ n ^ 2 % 9 = 7 := by
      have h : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
        omega
      rcases h with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
    omega
  · -- r = 8
    intro h
    rcases h with ⟨n, hn⟩
    have h1 : K % 9 = 8 := by 
      simp [hK1]
    have h2 : (Nat.digits 10 (n ^ 2)).sum % 9 = K % 9 := by 
      rw [hn]
    have h3 : (Nat.digits 10 (n ^ 2)).sum % 9 = n ^ 2 % 9 := by
      rw [Nat.modEq_nine_digits_sum (n ^ 2)]
    rw [h3] at h2
    rw [h1] at h2
    have h4 : n ^ 2 % 9 = 0 ∨ n ^ 2 % 9 = 1 ∨ n ^ 2 % 9 = 4 ∨ n ^ 2 % 9 = 7 := by
      have h : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
        omega
      rcases h with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
    omega