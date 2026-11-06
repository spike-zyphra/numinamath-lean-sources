import Mathlib

theorem number_theory_233704 (a b c : ℕ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : Nat.gcd (Nat.gcd a b) c = 15) (h₄ : a * b * c = 3000) :
    ¬Nat.gcd (Nat.gcd a b) c = 15 := by
  by_contra h 
  -- Since gcd(a,b,c) = 15, 15 divides a, b, c
  have h15 : Nat.gcd (Nat.gcd a b) c = 15 := by 
    omega 
  have h5 : 15 ∣ a := by 
    have h13 : (Nat.gcd (Nat.gcd a b) c) ∣ Nat.gcd a b := by 
      apply Nat.gcd_dvd_left
    have h26 : (Nat.gcd (Nat.gcd a b) c) = 15 := by 
      omega 
    have h14 : 15 ∣ Nat.gcd a b := by 
      rw [h26] at h13 
      exact h13 
    have h12 : Nat.gcd a b ∣ a := by 
      apply Nat.gcd_dvd_left
    exact Nat.dvd_trans h14 h12 
  -- Similarly, 15 divides b
  have h6 : 15 ∣ b := by 
    have h13 : (Nat.gcd (Nat.gcd a b) c) ∣ Nat.gcd a b := by 
      apply Nat.gcd_dvd_left
    have h26 : (Nat.gcd (Nat.gcd a b) c) = 15 := by 
      omega 
    have h14 : 15 ∣ Nat.gcd a b := by 
      rw [h26] at h13 
      exact h13 
    have h12 : Nat.gcd a b ∣ b := by 
      apply Nat.gcd_dvd_right
    exact Nat.dvd_trans h14 h12 
  -- Similarly, 15 divides c
  have h7 : 15 ∣ c := by 
    have h13 : (Nat.gcd (Nat.gcd a b) c) ∣ c := by 
      apply Nat.gcd_dvd_right
    have h26 : (Nat.gcd (Nat.gcd a b) c) = 15 := by 
      omega 
    rw [h26] at h13 
    exact h13 
  have h2' : 15 ∣ a := h5 
  obtain ⟨k, hk⟩ := h2' 
  have h2' : 15 ∣ b := h6 
  obtain ⟨l, hl⟩ := h2' 
  have h2' : 15 ∣ c := h7 
  obtain ⟨m, hm⟩ := h2' 
  have h11 : a = 15 * k := by linarith 
  have h12 : b = 15 * l := by linarith 
  have h13 : c = 15 * m := by linarith 
  rw [show a = 15 * k by linarith [hk], 
      show b = 15 * l by linarith [hl], 
      show c = 15 * m by linarith [hm]] at h₄ 
  have : (15 * k) * (15 * l) * (15 * m) = 3000 := h₄ 
  have : k * l * m * 3375 = 3000 := by 
    ring_nf at this ⊢ 
    linarith 
  omega