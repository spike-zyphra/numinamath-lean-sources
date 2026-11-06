import Mathlib

def f (n : ℤ) := if Odd n then n + 3 else n / 2

theorem number_theory_98454 (k : ℕ) (hk : Odd k) (h : f (f (f k)) = 27) :
    (Nat.digits 10 k).sum = 6 := by
  have h1 : k % 2 = 1 := by
    obtain ⟨m, hm⟩ := hk
    omega
  have hk2 : Odd (k : ℤ) := by
    obtain ⟨m, hm⟩ := hk
    use m
    all_goals omega
  have h3 : f k = (k : ℤ) + 3 := by
    simp [f, hk2]
  have h4 : f (f k) = ((k : ℤ) + 3) / 2 := by
    rw [h3]
    have h5 : ((k : ℤ) + 3 : ℤ) % 2 = 0 := by
      omega
    have h6 : ¬Odd ((k : ℤ) + 3 : ℤ) := by
      rw [Int.odd_iff]
      omega
    simp [f, h6]
  rw [h4] at h
  by_cases h7 : ((k : ℤ) + 3 : ℤ) / 2 % 2 = 1
  · -- if ((k + 3)/2) is odd
    have h8 : Odd (((k : ℤ) + 3 : ℤ) / 2 : ℤ) := by
      exact Int.odd_iff.mpr h7
    have h9 : f (((k : ℤ) + 3 : ℤ) / 2 : ℤ) = ((k : ℤ) + 3 : ℤ) / 2 + 3 := by
      simp [f, h8]
    rw [h9] at h
    omega
  · -- if ((k + 3)/2) is even
    have h8 : ¬Odd (((k : ℤ) + 3 : ℤ) / 2 : ℤ) := by
      rw [Int.odd_iff]
      omega
    have h9 : f (((k : ℤ) + 3 : ℤ) / 2 : ℤ) = (((k : ℤ) + 3 : ℤ) / 2 : ℤ) / 2 := by
      simp [f, h8]
    rw [h9] at h
    have h10 : ((k : ℤ) + 3 : ℤ) / 2 = 54 := by omega
    have h11 : (k : ℤ) = 105 := by omega
    have h12 : k = 105 := by omega
    subst k
    all_goals norm_num