import Mathlib


--Prove for integers $n$ that $$\left\lfloor\frac{n}{2}\right\rfloor \left\lfloor\frac{n + 1}{2}\right\rfloor = \left\lfloor\frac{n^2}{4}\right\rfloor.$$

theorem number_theory_611076 (n : ℤ) : ⌊n / 2⌋ * ⌊(n + 1) / 2⌋ = ⌊n^2 / 4⌋ := by
  -- We consider different cases based on whether n is even or odd.
  cases Int.even_or_odd n with
  | inl h_even =>  -- n is even
    have h_even : ∃ k, n = 2 * k := by simpa [Int.even_iff] using h_even
    rcases h_even with ⟨k, hk⟩
    have : ⌊n / 2⌋ = k := by
      simp [Int.floor_eq_iff, mul_comm]
      omega
    rw [this]
    have : ⌊(n + 1) / 2⌋ = k := by
      simp [Int.floor_eq_iff, mul_comm]
      omega
    rw [this]
    rw  [hk]
    ring_nf
    simp [Int.floor_eq_iff, mul_comm]
  | inr h_odd =>  -- n is odd
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := by 
      simpa [Int.odd_iff]     
    have : ⌊n / 2⌋ = k := by
      simp [Int.floor_eq_iff, mul_comm]
      omega
    rw [this]
    have : ⌊(n + 1) / 2⌋ = k + 1 := by
      simp [Int.floor_eq_iff, mul_comm]
      omega
    rw [this]
    have : ⌊n^2 / 4⌋ = k^2 + k := by
      rw[hk]
      simp[Int.floor_eq_iff,mul_comm]
      ring_nf
      omega  
    rw [this]
    ring