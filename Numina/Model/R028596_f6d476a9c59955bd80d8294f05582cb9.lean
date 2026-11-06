import Mathlib


/-
  Compute the number of ordered pairs of positive integers $(a, b)$ satisfying the equation

  $$
  \operatorname{gcd}(a, b) \cdot a+b^{2}=10000 .
  $$
-/
-- gcd(a, b)(l gcd(a, b)) + (rgcd(a, b)) ^ 2 = 10000
-- (l + r ^ 2) gcd(a,b) ^ 2 = 10000
theorem numbertheory_610534 (s : Set (ℕ × ℕ)) (hs : s = {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ Nat.gcd a b * a + b ^ 2 = 10000}) : 
    s.ncard = 99 := by 
  have h1 : s = Finset.filter (fun p => p.1 > 0 ∧ p.2 > 0 ∧ Nat.gcd p.1 p.2 * p.1 + p.2 ^ 2 = 10000) (Finset.Icc (0 : ℕ) 10000 ×ˢ Finset.Icc (0 : ℕ) 100) := by
    ext ⟨a, b⟩
    simp [hs]
    intro ha hb h
    have h1 : a ≤ 10000 := by
      have h1 : Nat.gcd a b * a ≤ Nat.gcd a b * a + b ^ 2 := by 
        linarith [show b ^ 2 ≥ 0 by positivity]
      have h2 : Nat.gcd a b * a + b ^ 2 = 10000 := h
      have h3 : Nat.gcd a b * a ≤ 10000 := by 
        linarith [h1, h2]
      have h4 : a ≤ 10000 := by 
        by_contra h4
        push_neg at h4
        have h5 : Nat.gcd a b ≥ 1 := by
          have ha' : a > 0 := ha
          have hb' : b > 0 := hb
          have h4 : Nat.gcd a b > 0 := by
            apply Nat.gcd_pos_of_pos_left 
            exact ha'
          linarith [h4]
        nlinarith [h3, h4, h5]
      linarith
    have h2 : b ≤ 100 := by 
      have h1 : b ^ 2 ≤ Nat.gcd a b * a + b ^ 2 := by 
        have ha' : Nat.gcd a b * a ≥ 0 := by positivity 
        linarith [ha']
      have h2 : Nat.gcd a b * a + b ^ 2 = 10000 := h
      have h3 : b ^ 2 ≤ 10000 := by 
        linarith [h1, h2]
      have h4 : b ≤ 100 := by nlinarith
      exact h4
    simp [Finset.mem_Icc, h1, h2]
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide